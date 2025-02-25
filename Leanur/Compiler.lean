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
-- open Leanur.Nock.DSL
open Leanur.Nock.Interpreter

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
  | List : MemRepList → MemRep         -- Special representations for List-like types
  | Maybe : MemRepMaybe → MemRep       -- Special representations for Option-like types
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
def emptyCompilerCtx (env : Lean.Environment) : CompilerCtx where
  env := env
  overrides := {}
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
def emptyCompilerState : CompilerState where
  appendedBindings := #[]
  visited := {}
  replaced := {}

/-- The monad for our compilation process -/
abbrev CompilerM (α : Type) := ReaderT CompilerCtx (StateRefT CompilerState IO) α

end Leanur.Compiler
