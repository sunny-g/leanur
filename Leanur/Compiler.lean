import Lean
import Lean.CoreM
import Leanur.Nock

/-!
  CodeGen module for converting Lean's LCNF (Low-level Continuation-passing Normal Form)
  to Nock's Noun AST. This allows us to execute Lean code on a Nock interpreter.

  This module implements the compiler that translates Lean4 to Nock, following a similar approach to
  Juvix's Nockma backend but tailored for Lean's LCNF representation.
-/
namespace Leanur.Compiler

open Std
open Lean.Core
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
  | Slot                                -- @ - Fetch data at a path
  | Quote                               -- Quote literal data
  | Apply                               -- Apply a function
  | IsCell                              -- Test if a value is a cell
  | Inc                                 -- Increment
  | Eq                                  -- Equality test
  | If                                  -- Conditional branching
  | Seq                                 -- Sequence operations
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
  -- tempVarMap : Lean.FVarIdMap TempRef
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
abbrev CompilerM := ReaderT CompilerCtx $ StateRefT CompilerState CoreM

/-!
  ### Core Utility Functions

  These functions provide the essential utilities for our compiler:
  - Stack management (push/pop temporary variables)
  - Path manipulation
  - Name handling
  - Tracking visited declarations
-/

/-- Convert a path to a Nock noun for lookup -/
private def pathToNoun : Path → Noun
  | .Left => atom 2      -- Left path is 2 in Nock
  | .Right => atom 3     -- Right path is 3 in Nock
  | .Cons p1 p2 =>
    -- In Nock, path composition is done by computing the right address
    -- For simplicity, we'll just compose the cells for now
    cell (pathToNoun p1) (pathToNoun p2)
instance : ToNoun Path where toNoun := pathToNoun

/-- Convert a Lean literal to a Nock noun -/
instance : ToNoun Lean.Literal where toNoun : Lean.Literal → Noun
  | .natVal n => n
  | .strVal s =>
    -- For now, we'll represent strings as a linked list of character atoms
    -- A more efficient implementation would use a different encoding
    let chars := s.toList.map (fun c => atom c.toNat)
    let rec buildList : List Noun → Noun
      | [] => atom 0  -- nil represented as 0
      | x::xs => cell x (buildList xs)
    buildList chars

/-- Mark a declaration as visited -/
private def visit (name : Lean.Name) : CompilerM Unit := do
  modify fun s => { s with visited := s.visited.insert name }

/-- Check if a declaration has been visited -/
private def isVisited (name : Lean.Name) : CompilerM Bool := do
  return (← get).visited.contains name

/-- Create a fresh name to replace another name -/
private def replaceName (name : Lean.Name) : CompilerM Lean.Name := do
  let name' := Lean.Name.mkNum Lean.Name.anonymous ((← get).appendedBindings.size + 1)
  modify fun s => { s with replaced := s.replaced.insert name name' }
  return name'

/-- Get a safe name (handling conflicts) -/
private def safeName (name : Lean.Name) : CompilerM Lean.Name := do
  match (← get).replaced.find? name with
  | some n => pure n
  | none   => replaceName name

/-- Append a binding to the compiled output -/
private def appendBinding (name : Lean.Name) (value : Noun) : CompilerM Unit := do
  let name ← safeName name
  modify fun s => { s with appendedBindings := s.appendedBindings.push (name, value) }

section Ops

/-- Create a Nock address expression for a path -/
private def opSlot (tag : String) (path : Path) : Noun :=
  -- Nock address operator (0) with the path
  cell 0 (ToNoun.toNoun path)

/-- Create a quoted literal value -/
private def opQuote (lit : Lean.Literal) : Noun :=
  -- Use Nock quote operator (1) to create a literal value
  cell 1 (ToNoun.toNoun lit)

/-- Create a Nock equality test -/
private def opEq (l r : Noun) : Noun :=
  -- Nock op 5 [l r]
  cell 5 (cell l r)

/-- Create a Nock if-then-else expression -/
private def opIf (cond then_ else_ : Noun) : Noun :=
  -- Nock op 6 [cond [true false]]
  cell 6 (cell cond (cell then_ else_))

/-- Create a Nock composition (sequence) -/
private def opSeq (f g : Noun) : Noun :=
  -- Nock op 7 [f g]
  cell 7 (cell f g)

/-- Create a Nock push expression -/
private def opPush (val body : Noun) : Noun :=
  cell 8 (cell (cell 1 val) body)

/-- Create a Nock call expression -/
private def opCall (fn args : Noun) : Noun :=
  -- Nock op 9 [args fn]
  cell 9 (cell args fn)

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
  return opSlot s!"tempRef-{ref.index}" path

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
  return opPush value body

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

-- /-- Run the compiler monad -/
-- def runCompilerM (env : Lean.Environment) (m : CompilerM α) : EStateM.Result String CompilerState α :=
--   let ctx := CompilerCtx.fromEnv env
--   m ctx |>.run CompilerState.empty

section Compiler

/-- Compile a literal to a Nock expression -/
def mkLiteral (lit : Lean.Literal) : CompilerM Noun := do
  return opQuote lit

/-- Compile a local variable reference -/
def mkLocalVar (fvarId : Lean.FVarId) : CompilerM Noun := do
  -- Find the temp ref for this variable
  let tempVar := (← read).tempVarMap.get? fvarId.name.hash.toNat
  match tempVar with
  | none => throwError s!"Unknown variable: {fvarId.name}"
  | some ref => addressTempRef ref

mutual

/-- Compile function/constructor arguments -/
partial def mkArgs (args : Array Lean.Expr) : CompilerM (List Noun) := do
  let mut result : List Noun := []
  for arg in args do
    let argNoun ← mkExpr arg
    result := result.concat argNoun
  return result

/-- Compile a Lean expression to Nock -/
partial def mkExpr (expr : Lean.Expr) : CompilerM Noun := do
  match expr with
  -- bvar, mvar
  | .fvar fvarId => mkLocalVar fvarId
  | .lit lit => mkLiteral lit
  -- sort
  | .const name _ => do
    -- Handle constant reference (could be a function or constructor)
    -- Check if we have an override for this name
    let overrides := (← read).overrides
    match overrides.find? name with
    | some (.expr noun) => return noun
    | none =>
      -- Get the constant path in our function library
      let functionId := FunctionId.User name
      let functionInfos := (← read).functionInfos
      match functionInfos.get? functionId with
      | none => throwError s!"Unknown function: {name}"
      | some info =>
        -- Create a reference to the function in the library
        return opSlot s!"function-{name}" info.path
  | .app fn arg => do
    -- Handle function application
    let fnNoun ← mkExpr fn
    let argNoun ← mkExpr arg
    -- In Nock, application is done using the call operator (9)
    return opCall fnNoun argNoun
  -- lam, forallE, letE, mdata, proj
  | _ => throwError s!"Unsupported expression: {expr}"

/-- Compile a let value (right-hand side of binding) -/
partial def mkLetValue (value : LetValue) : CompilerM Noun := do
  match value with
  | .erased => return atom 0  -- Erased values represented as 0
  | .value val => mkExpr val.toExpr
  | .fvar fvarId args => mkLocalVar fvarId
  | .const declName _ args => do
    -- Handle constant reference with arguments (function call or constructor)
    let functionId := FunctionId.User declName
    let functionInfos := (← read).functionInfos

    -- Check if we have an override for this constant
    let overrides := (← read).overrides
    match overrides.find? declName with
    | some (.expr noun) =>
      -- For overrides, assume all arguments are already applied
      return noun
    | none =>
      match functionInfos.get? functionId with
      | none => throwError s!"Unknown function in call: {declName}"
      | some info =>
        -- Function call with arguments
        let fnRef := opSlot s!"function-{declName}" info.path
        if args.isEmpty then
          return fnRef
        else
          -- Apply arguments
          let argNouns ← mkArgs (args.map Arg.toExpr)
          -- Function calling convention using Nock call (9)
          -- Pack arguments into a tuple
          let argsNoun := argNouns.foldl (fun acc arg => cell acc arg) 0
          return opCall fnRef argsNoun
  | .proj _ i fvarId => do
    -- Projection accesses a field of a constructor
    -- First, get the reference to the constructor value
    let valueRef ← mkLocalVar fvarId
    -- Then extract the field at position i using Nock's address operator (0)
    -- We need to calculate the slot path based on field index
    -- For a zero-based index i, the slot would be 2 + i
    let slotNum := 2 + i
    return cell 0 (cell slotNum valueRef)

  -- | .jp fvarId args => do
  --   -- Jump is essentially a function call to a local variable
  --   let fnRef ← compileLocalVar fvarId
  --   if args.isEmpty then
  --     return fnRef
  --   else
  --     -- Apply arguments
  --     let argNouns ← compileArgs args
  --     -- Function calling convention using Nock call (9)
  --     -- Pack arguments into a tuple
  --     let argsNoun := argNouns.foldl (fun acc arg => cell acc arg) (atom 0)
  --     return makeCall fnRef argsNoun

  -- | _ => throwError s!"Unsupported let value: {value}"

/-- Compile a let declaration (variable and its value) -/
partial def mkLetDecl (decl : LetDecl) : CompilerM Noun := do
  let valueNoun ← mkLetValue decl.value

  -- Bind the value to a temporary variable
  withTempVar valueNoun fun ref => do
    -- Register this variable in our context
    let varId := decl.fvarId
    withReader (fun ctx => {
      ctx with tempVarMap := ctx.tempVarMap.insert varId.name.hash.toNat ref
    }) (pure valueNoun)

/-- Create a constructor for an alternative case -/
partial def mkCaseAltCondition (fvarId : Lean.FVarId) (ctorName : Lean.Name) (ctorIdx : Nat) : CompilerM Noun := do
  -- Get the value we're matching against
  let scrutinee ← mkLocalVar fvarId

  -- Check if the constructor tag matches ctorIdx
  -- First, access the tag field (typically the first field of a constructor value)
  let tagAccess := cell 0 (cell 2 scrutinee)

  -- Then compare it with the constructor index
  return opEq tagAccess (atom ctorIdx)

/-- Compile an alternative in a case expression -/
partial def mkCaseAlt (fvarId : Lean.FVarId) (alt : Alt) : CompilerM Noun := do
  match alt with
  | .default code =>
    -- Default case - just compile the code
    mkCode code

  | .alt ctorName fields code => do
    -- Constructor pattern - compile code with bindings for the fields
    let scrutinee ← mkLocalVar fvarId

    -- Create bindings for the fields
    withTemp scrutinee fun scrutRef => do
      -- Add bindings for the fields
      for i in [:fields.size] do
        let fieldRef : TempRef := { index := (← read).stackHeight + i }
        let field := fields[i]!

        -- Create a binding for the field
        -- Field access via Nock address (0)
        -- For a constructor, fields start at position 3 (after the tag and constructor name)
        let fieldPath := i + 3
        let fieldAccess := cell 0 (cell fieldPath (← addressTempRef scrutRef))

        -- Push this field onto the stack
        -- TODO: shouldnt we output this underscore value?
        let _ ← withTemp fieldAccess fun fRef => do
          -- Register the field in our context
          withReader (fun ctx => {
            ctx with tempVarMap := ctx.tempVarMap.insert field.fvarId.name.hash.toNat fRef
          }) (pure (atom 0))

      -- Finally, compile the case body with the fields in scope
      mkCode code

/-- Compile a case expression -/
partial def mkCase (fvarId : Lean.FVarId) (alts : Array Alt) : CompilerM Noun := do
  -- No alternatives is an error
  if alts.isEmpty then
    throwError "Empty case expression"

  -- If there's only a default case, just compile it
  if alts.size == 1 && alts[0]! matches .default _ then
    mkCaseAlt fvarId alts[0]!
  else
    -- We'll implement pattern matching using Nock's conditional operator (6)
    -- Build a chain of if-then-else expressions

    -- Process all alternatives
    let mut result : Option Noun := none

    -- Start from the last alternative and work backwards
    for alt in alts.reverse do
      let altNoun ← match alt with
        -- Default case - compile the code
        | .default code => mkCode code
        -- Constructor case - check the tag and compile the body TODO:
        | .alt ctorName _ code => do
          let condition ← mkCaseAltCondition fvarId ctorName _
          mkCaseAlt fvarId alt

      match result with
      -- This is the last (or only) alternative
      | none => result := altNoun
      | some elseNoun => match alt with
        -- Build an if-then-else using Nock op 6
        -- Default case always matches
        | .default _ => result := altNoun
        -- Constructor case - create a condition TODO:
        | .alt ctorName _ _ =>
          let condition ← mkCaseAltCondition fvarId ctorName _
          result := opIf condition altNoun elseNoun

    -- Return the final pattern matching expression
    pure (result.getD 0)

/-- Main entry point for compiling LCNF code -/
partial def mkCode (code : Code) : CompilerM Noun := do
  match code with
  | .let decl cont => do
    -- Compile the declaration
    let declNoun ← mkLetDecl decl

    -- Then compile the continuation with the declaration in scope
    withTemp declNoun fun _ => do
      mkCode cont

  | .fun decl cont
  | .jp decl cont => do
    throwError s!"TODO: unimplemented"

  | .jmp fvarId args => do
    -- Jump is function application
    let value : LetValue := .fvar fvarId args
    mkLetValue value

  | .cases cases => do
    -- Pattern matching
    mkCase cases.discr cases.alts

  | .return fvarId => do
    -- Return a value
    mkLocalVar fvarId

  | .unreach _ =>
    -- Unreachable code
    pure (atom 0)


/-- Compile a function declaration (w/ params and body) -/
partial def mkFunDecl (decl : FunDecl) : CompilerM Noun := do
  -- Handle parameters by creating bindings for them
  let mut bodyCompiler : CompilerM Noun := pure (atom 0)

  -- Start with the innermost parameter and work outwards
  let mut params := decl.params.toList

  -- Compile the function body with parameters in scope
  bodyCompiler := do
    -- Create a binding for each parameter
    for param in params do
      -- Create a reference to the parameter
      let paramRef : TempRef := { index := (← read).stackHeight - params.idxOf param - 1 }
      -- Add it to our environment
      -- TODO: shouldnt we output this underscore value?
      let _ ← withReader (fun ctx => {
        ctx with tempVarMap := ctx.tempVarMap.insert param.fvarId.name.hash.toNat paramRef
      }) (pure (atom 0))

    -- Finally, compile the actual function body
    mkCode decl.value

  -- Create a closure that captures the function body and parameters
  -- The closure is represented as a cell with:
  -- [param1 [param2 ... [paramN body]...]]
  let mut result ← bodyCompiler
  for param in params.reverse do
    -- Wrap each parameter around the body
    result := cell param.fvarId.name.hash.toNat result

  return result

/-- Process a declaration and compile it to Nock -/
partial def mkDecl (declName : Lean.Name) : CompilerM Noun := do
  -- Check if this declaration has already been processed
  if (← isVisited declName) then
    -- Find the compiled binding
    let state ← get
    let bindings := state.appendedBindings
    for (name, value) in bindings do
      if name == declName then
        return value

    throwError s!"Declaration {declName} was visited but not found in bindings"

  -- Mark as visited to prevent cycles
  visit declName

  -- Get the declaration from the environment
  let env := (← read).env
  match env.find? declName with
  | none => throwError s!"Declaration {declName} not found"
  | some _ => do
    -- Get the LCNF representation
    match (← getDecl? declName) with
    | some (.funDecl funDecl) => do
      -- Compile the function declaration
      let noun ← mkFunDecl funDecl
      -- Add it to our bindings
      appendBinding declName noun
      return noun

    | some (.paramDecl _) => do
      -- Handle parameters (type parameters, etc.)
      let noun := atom 0  -- Simple representation for now
      appendBinding declName noun
      return noun

    | some (.recFunDecl recFunDecls) => do
      -- Handle mutually recursive functions
      throwError "Recursive function declarations not yet implemented"

    | some (.letDecl letDecl) => do
      -- Handle let declarations
      let valNoun ← mkLetValue letDecl.value
      appendBinding declName valNoun
      return valNoun

    | none => do
      -- If no LCNF representation, create a simple constant
      let noun := atom declName.hash
      appendBinding declName noun
      return noun

end

end Compiler

end Leanur.Compiler
