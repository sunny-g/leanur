import Lean
import Leanur.Nock

/-!
  CodeGen module for converting Lean's LCNF (Low-level Continuation-passing Normal Form)
  to Nock's Noun AST. This allows us to execute Lean code on a Nock interpreter.

  This module implements the compiler that translates Lean4 to Nock, following a similar approach to
  Juvix's Nockma backend but tailored for Lean's LCNF representation.
-/
namespace Leanur.Compiler

open Std
open Lean.Compiler.LCNF
open Leanur.Nock
open Leanur.Nock.Noun
-- open Leanur.Nock.DSL
open Leanur.Nock.Interpreter

section Types

/-!
  ### Core Data Structures

  These types form the foundation of our compiler. They represent:
  - Constructor and function identifiers
  - Memory representations for different data types
  - Temporary variable tracking for stack-based compilation
  - Path tracking for accessing elements in Nock's subject
-/

/-- Reference to a variable on the temporary compilation stack -/
structure TempRef where
  index : Nat
  deriving BEq, Hashable

/-- Path to a value in the Nock subject -/
inductive Path where
  | Left : Path
  | Right : Path
  | Cons : Path → Path → Path
  deriving BEq, Hashable

/-- Tags for constructors, either built-in or user-defined -/
inductive Tag where
  | Builtin : String → Tag              -- Built-in type tags (Bool, Nat, etc.)
  | User : Lean.Name → Nat → Tag        -- User-defined type tag (inductiveName, constructorIdx)
  deriving BEq, Hashable

/-- Memory representation for algebraic data types -/
inductive MemRepList where | Nil | Cons deriving BEq, Hashable
inductive MemRepMaybe where | None | Some deriving BEq, Hashable
inductive MemRep where
  | Constr                              -- Generic constructor [tag args]
  | Tuple                               -- Tuple representation (single constructor types)
  | List : MemRepList → MemRep          -- Special representations for List-like types
  | Maybe : MemRepMaybe → MemRep        -- Special representations for Option-like types
  deriving BEq, Hashable

/-- Variants for List-like types -/
inductive ListVariant where
  | Nil                                 -- Empty list constructor
  | Cons                                -- Cons cell constructor
  deriving BEq, Hashable

/-- Variants for Maybe-like types -/
inductive MaybeVariant where
  | None                                -- None constructor
  | Some                                -- Some constructor
  deriving BEq, Hashable

/-- Built-in Nock native operations -/
inductive NockOp where
  | Address                             -- @ - Fetch data at a path
  | Quote                               -- Quote literal data
  | Apply                               -- Apply a function
  | IsCell                              -- Test if a value is a cell
  | Inc                                 -- Increment
  | Eq                                  -- Equality test
  | If                                  -- Conditional branching
  | Sequence                            -- Sequence operations
  | Push                                -- Push onto subject stack
  | Call                                -- Function call
  | Replace                             -- Modify the subject
  | Hint                                -- Add runtime hints
  deriving BEq, Hashable, Repr

/-- Function identifier, either user-defined or built-in -/
inductive FunctionId where
  | User : Lean.Name → FunctionId       -- User-defined function
  | Builtin : String → FunctionId       -- Built-in function
  deriving BEq, Hashable

/-- Information about a compiled function -/
structure FunctionInfo where
  path : Path                           -- Path to the function in the function library
  arity : Nat                           -- Number of arguments
  name : String                         -- Human-readable name
  -- deriving Inhabited

/-- Information about a constructor -/
structure ConstructorInfo where
  arity : Nat                           -- Number of fields
  memRep : MemRep                       -- Memory representation strategy
  -- deriving Inhabited

/-- Enumeration of fields in a closure -/
inductive ClosureField where
  | FunCode                             -- Function code
  | ArgsTuple                           -- Arguments tuple
  | RemainingArgsNum                    -- Number of remaining arguments (for currying)
  | FunctionsLibrary                    -- Library of available functions
  deriving BEq, Hashable, Repr

/-- Special handling for primitive operations -/
inductive Override where
  | expr : Noun → Override              -- Direct Nock expression override
  -- | compile : List Noun → CompilerM Noun  -- Custom compilation function

/-- Stack of bindings used during compilation -/
structure BindingStack where
  bindings : List (Lean.Name × Noun)
  deriving Inhabited

end Types

/-- Compiler context containing environment and metadata -/
structure CompilerCtx where
  env : Lean.Environment                 -- Lean environment containing declarations
  overrides : Lean.NameMap Override      -- Special handling for built-in ops
  functionInfos : HashMap FunctionId FunctionInfo  -- Function metadata
  constructorInfos : HashMap Tag ConstructorInfo   -- Constructor metadata
  tempVarMap : HashMap Nat TempRef       -- Manages temporary variable stack
  tempVarsNum : Nat                      -- Counter for temporary variables
  stackHeight : Nat                      -- Current stack height for Nock compilation
  -- deriving Inhabited

/-- Initial empty compiler context -/
def CompilerCtx.fromEnv (env : Lean.Environment) (overrides : Lean.NameMap Override := {}) : CompilerCtx where
  env := env
  overrides := overrides
  functionInfos := {}
  constructorInfos := {}
  tempVarMap := {}
  tempVarsNum := 0
  stackHeight := 0

/-- Compiler state during compilation -/
structure CompilerState where
  appendedBindings : Array (Lean.Name × Noun)  -- Compiled bindings
  visited : Lean.NameSet                        -- Visited declarations
  replaced : Lean.NameMap Lean.Name             -- Renamed declarations
  deriving Inhabited

/-- Initial empty compiler state -/
def CompilerState.empty : CompilerState where
  appendedBindings := #[]
  visited := {}
  replaced := {}

/-- The monad for our compilation process -/
abbrev CompilerM (α : Type) := ReaderT CompilerCtx (EStateM String CompilerState) α

/-!
  ### Core Utility Functions

  These functions provide the essential utilities for our compiler:
  - Stack management (push/pop temporary variables)
  - Path manipulation
  - Name handling
  - Tracking visited declarations
-/

/-- Mark a declaration as visited -/
private def visit (name : Lean.Name) : CompilerM Unit := do
  modify fun s => { s with visited := s.visited.insert name }

/-- Check if a declaration has been visited -/
private def isVisited (name : Lean.Name) : CompilerM Bool := do
  return (← get).visited.contains name

/-- Create a fresh name to replace another name -/
private def replaceName (name : Lean.Name) : CompilerM Lean.Name := do
  let name' := Lean.Name.mkNum Lean.Name.anonymous ((← get).appendedBindings.size + 1)
  modify fun s => { s with
    replaced := s.replaced.insert name name'
  }
  return name'

/-- Get a safe name (handling conflicts) -/
private def safeName (name : Lean.Name) : CompilerM Lean.Name := do
  match (← get).replaced.find? name with
  | some n => return n
  | none   => replaceName name

/-- Append a binding to the compiled output -/
private def appendBinding (name : Lean.Name) (value : Noun) : CompilerM Unit := do
  let name ← safeName name
  modify fun s => { s with
    appendedBindings := s.appendedBindings.push (name, value)
  }

/-- Convert a path to a Nock noun for lookup -/
def pathToNoun (path : Path) : Noun :=
  match path with
  | .Left => atom 2      -- Left path is 2 in Nock
  | .Right => atom 3     -- Right path is 3 in Nock
  | .Cons p1 p2 =>
      -- In Nock, path composition is done by computing the right address
      -- For simplicity, we'll just compose the cells for now
      cell (pathToNoun p1) (pathToNoun p2)

/-- Convert a Lean literal to a Nock noun -/
def literalToNoun (lit : Lean.Literal) : Noun :=
  match lit with
  | .natVal n => atom n
  | .strVal s =>
    -- For now, we'll represent strings as a linked list of character atoms
    -- A more efficient implementation would use a different encoding
    let chars := s.toList.map (fun c => atom c.toNat)
    let rec buildList : List Noun → Noun
      | [] => atom 0  -- nil represented as 0
      | x::xs => cell x (buildList xs)
    buildList chars

section Ops

/-- Create a Nock address expression for a path -/
def addressPath (tag : String) (path : Path) : Noun :=
  -- Nock address operator (0) with the path
  cell (atom 0) (pathToNoun path)

/-- Create a quoted literal value -/
def quotedLiteral (lit : Lean.Literal) : Noun :=
  -- Use Nock quote operator (1) to create a literal value
  cell (atom 1) (literalToNoun lit)

end Ops

section Stack

/-- Calculate a path to a stack position -/
def stackPath (idx : Nat) : CompilerM Path := do
  let height := (← read).stackHeight
  -- Create a path with enough Rights to reach the correct depth, then a Left
  -- This translates to going down the right branches of the tree until we reach the correct depth
  let rec buildPath (n : Nat) : Path :=
    match n with
      | 0 => Path.Left
      | Nat.succ n => Path.Cons Path.Right (buildPath n)
  return buildPath (height - idx - 1)

/-- Calculate the path to a temporary variable -/
def tempRefPath (ref : TempRef) : CompilerM Path :=
  stackPath ref.index

/-- Get a Nock address expression for a temporary variable -/
def addressTempRef (ref : TempRef) : CompilerM Noun := do
  let path ← tempRefPath ref
  return addressPath s!"tempRef-{ref.index}" path

/-- The critical withTemp function pushes a value onto the subject stack -/
def withTemp (value : Noun) (f : TempRef → CompilerM Noun) : CompilerM Noun := do
  let stackHeight := (← read).stackHeight
  let ref : TempRef := { index := stackHeight }

  -- Execute f with increased stack height
  let body ← withReader
    (fun ctx => { ctx with stackHeight := ctx.stackHeight + 1 })
    (f ref)

  -- Create a Nock expression that uses the Push operator (8)
  -- [8 [1 value] body] in Nock means: push value onto the subject, then evaluate body
  return cell (atom 8) (cell (cell (atom 1) value) body)

/-- Push and track a temporary variable -/
def withTempVar (value : Noun) (f : TempRef → CompilerM Noun) : CompilerM Noun := do
  let tempVar := (← read).tempVarsNum
  withTemp value fun ref => do
    -- Register the temp var in our map
    withReader (fun ctx => {
      ctx with
        tempVarMap := ctx.tempVarMap.insert tempVar ref,
        tempVarsNum := ctx.tempVarsNum + 1
    }) (f ref)

/-- Pop a temporary variable -/
def popTempVar (cont : CompilerM Noun) : CompilerM Noun := do
  let tempVar := (← read).tempVarsNum
  withReader (fun ctx => {
    ctx with
      tempVarMap := ctx.tempVarMap.erase (tempVar - 1),
      tempVarsNum := ctx.tempVarsNum - 1
  }) cont

end Stack

/-- Run the compiler monad -/
def runCompilerM (env : Lean.Environment) (m : CompilerM α) : EStateM.Result String CompilerState α :=
  let ctx := CompilerCtx.fromEnv env
  m ctx |>.run CompilerState.empty

end Leanur.Compiler
