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


/-- Create a constructor for algebraic data types -/
def mkConstructor (tag : Tag) (fields : List Noun) : CompilerM Noun := do
  -- Get constructor info if available
  let ctorInfo ← match (← read).constructorInfos.get? tag with
    | some info => pure info
    | none =>
      -- Default to generic constructor representation if not found
      pure { arity := fields.length, memRep := MemRep.Constr }

  -- Different memory representations for different constructor types
  match ctorInfo.memRep with
  | .Constr =>
    -- Generic constructor: [tag field1 field2 ...]
    -- First create the tag value
    let tagNoun := match tag with
      | .Builtin name => atom name.hash.toNat -- Built-in tags as hashed atoms
      | .User name idx => atom idx      -- User-defined tags as index atoms

    -- Then fold all fields into a nested cell structure
    let fieldsNoun := fields.foldl (fun acc field => cell acc field) tagNoun
    pure fieldsNoun

  | .Tuple =>
    -- For single constructor types (records), don't include tag
    -- Just create a tuple of fields
    let fieldsNoun := fields.foldl (fun acc field => cell acc field) (atom 0)
    pure fieldsNoun

  | .List variant =>
    -- Special encoding for list-like types
    match variant with
    | .Nil => pure (atom 0)  -- Empty list is atom 0
    | .Cons =>
      -- Cons cell is [head tail]
      if fields.length >= 2 then
        let head := fields[0]!
        let tail := fields[1]!
        pure (cell head tail)
      else
        throwError "Cons constructor requires at least 2 fields"

  | .Maybe variant =>
    -- Special encoding for Maybe-like types
    match variant with
    | .None => pure (atom 0)  -- None is atom 0
    | .Some =>
      -- Some is the value directly (unwrapped)
      if fields.length >= 1 then
        pure fields[0]!
      else
        throwError "Some constructor requires at least 1 field"


mutual

/-- Compile function/constructor arguments -/
partial def mkArgs (args : Array Lean.Expr) : CompilerM (List Noun) := do
  let mut result : List Noun := []
  for arg in args do
    let argNoun ← mkExpr arg
    result := result ++ [argNoun]
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
    match (← read).overrides.find? name with
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
  -- lam, forallE, letE, proj
  | .letE declName type value body _ => do
    -- let ($n : $t) := $v in $b
    throwError s!"Expr.letE unimplemented"
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
    match (← read).overrides.find? declName with
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

    -- Create bindings for the fields in a function that we compose manually
    -- rather than using for-loops which can create type mismatches
    let setupFields : CompilerM Noun := do
      -- Set up a nested function to handle all fields
      let rec processFields (i : Nat) : CompilerM Noun := do
        if i >= fields.size then
          -- When all fields are processed, compile the code
          mkCode code
        else
          -- Process current field and then recursively handle the next one
          let field := fields[i]!
          -- Field access via Nock address (0)
          -- For a constructor, fields start at position 3 (after tag and name)
          let fieldPath := i + 3
          let fieldAccess := cell (atom 0) (cell (atom fieldPath) scrutinee)

          -- Push field onto stack and process next field
          withTemp fieldAccess fun fRef => do
            -- Register field in our context
            withReader (fun ctx => {
              ctx with tempVarMap := ctx.tempVarMap.insert field.fvarId.name.hash.toNat fRef
            }) (processFields (i + 1))

      -- Start processing from the first field
      processFields 0

    -- Create the final expression using withTemp for the scrutinee
    withTemp scrutinee fun _ => setupFields

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
        -- Constructor case - check the tag and compile the body
        | .alt ctorName fields code => do
          -- Get the constructor index from the environment
          let env := (← read).env
          -- For now, we'll use a simple approach - ctor index is 0 if unknown
          let ctorIdx :=
            match env.find? ctorName with
            | some (.ctorInfo ctorVal) => ctorVal.cidx
            | _ => 0  -- Default index if not found
          let condition ← mkCaseAltCondition fvarId ctorName ctorIdx
          mkCaseAlt fvarId alt

      match result with
      -- This is the last (or only) alternative
      | none => result := some altNoun
      | some elseNoun => match alt with
        -- Build an if-then-else using Nock op 6
        -- Default case always matches
        | .default _ => result := some altNoun
        -- Constructor case - create a condition
        | .alt ctorName fields _ =>
          -- Get the constructor index again
          let env := (← read).env
          let ctorIdx :=
            match env.find? ctorName with
            | some (.ctorInfo ctorVal) => ctorVal.cidx
            | _ => 0  -- Default index if not found
          let condition ← mkCaseAltCondition fvarId ctorName ctorIdx
          result := some (opIf condition altNoun elseNoun)

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

  | .fun decl cont => do
    -- Compile a local function declaration
    let funNoun ← mkFunDecl decl

    -- Add the function to the environment
    withTempVar funNoun fun funRef => do
      -- Register the function in our context
      withReader (fun ctx => {
        ctx with tempVarMap := ctx.tempVarMap.insert decl.fvarId.name.hash.toNat funRef
      }) (mkCode cont)
  | .jp decl cont => do
    -- Jump is essentially a function call to a local variable
    let fnRef ← mkLocalVar decl.fvarId
    let args := decl.params.map (Param.toExpr)
    if args.isEmpty then
      return fnRef
    else
      -- Apply arguments
      let argNouns ← mkArgs args
      -- Function calling convention using Nock call (9)
      -- Pack arguments into a tuple
      let argsNoun := argNouns.foldl (fun acc arg => cell acc arg) (atom 0)
      return opCall fnRef argsNoun

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
  let params := decl.params.toList

  -- Use a recursive approach to set up parameters to avoid for-loop type issues
  let rec setupParamsAndCompileBody (i : Nat) (ctx : CompilerCtx) : CompilerM Noun :=
    if i >= params.length then
      -- When all parameters are set up, compile the body with the updated context
      withReader (fun _ => ctx) (mkCode decl.value)
    else
      -- Process current parameter and continue to the next one
      let param := params[i]!
      -- Calculate reference to parameter in the stack
      let paramRef : TempRef := { index := ctx.stackHeight - i - 1 }
      -- Update context with this parameter binding
      let newCtx := {
        ctx with
        tempVarMap := ctx.tempVarMap.insert param.fvarId.name.hash.toNat paramRef
      }
      -- Process the next parameter with updated context
      setupParamsAndCompileBody (i+1) newCtx

  -- Get current context to start the process
  let currentCtx ← read
  -- Compile body with all parameters in scope
  let body ← setupParamsAndCompileBody 0 currentCtx

  -- Build the function representation from the inside out
  -- The closure is represented as a cell with:
  -- [param1 [param2 ... [paramN body]...]]
  let mut result := body
  for param in params.reverse do
    -- Wrap each parameter around the body
    result := cell (atom param.fvarId.name.hash.toNat) result

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
  | some constInfo => do
    -- We can't directly use getDecl? as it returns a different monad
    -- Process based on the constant info type
    match constInfo with
    | .defnInfo val => do
      -- Create a simplified function representation
      let arity := val.type.getForallArity

      -- For recursive functions, we need a placeholder approach
      -- For now, create a simple representation
      let noun := cell arity declName.hash.toNat
      appendBinding declName noun
      return noun

    | .ctorInfo val => do
      -- Create a constructor function
      let tag := Tag.User val.induct val.cidx
      let ctorInfo := {
        arity := val.numFields,
        memRep := MemRep.Constr
      }
      -- Register the constructor info
      withReader (fun ctx => {
        ctx with constructorInfos := ctx.constructorInfos.insert tag ctorInfo
      }) (pure ())

      -- Return a representation of the constructor as a function
      let noun := cell val.cidx declName.hash.toNat
      appendBinding declName noun
      return noun

    | .axiomInfo val => do
      -- Handle axiom - create a constant value
      let noun := atom declName.hash.toNat
      appendBinding declName noun
      return noun

    | .thmInfo val => do
      -- Handle theorem - similar to definition
      let arity := val.type.getForallArity
      let noun := cell arity declName.hash.toNat
      appendBinding declName noun
      return noun

    | .opaqueInfo val => do
      -- Handle opaque definition - similar to definition
      let arity := val.type.getForallArity
      let noun := cell arity declName.hash.toNat
      appendBinding declName noun
      return noun

    | .quotInfo val => do
      -- Handle quotient type
      let noun := atom declName.hash.toNat
      appendBinding declName noun
      return noun

    | .inductInfo val => do
      -- Handle inductive type
      let noun := atom declName.hash.toNat
      appendBinding declName noun
      return noun

    | .recInfo val => do
      -- Handle recursor
      let arity := val.type.getForallArity
      let noun := cell arity declName.hash.toNat
      appendBinding declName noun
      return noun

end

end Compiler

/-- Add standard Nock prelude with overrides for basic operations -/
def addNockPrelude (ctx : CompilerCtx) : CompilerCtx :=
  -- Add standard overrides for primitive operations
  let ctx := { ctx with
    overrides := ctx.overrides.insert `Nat.add (.expr (cell 7 (cell (cell 4 (cell 0 3)) (cell 0 2))))
  }

  -- Add specialized representations for common types
  let ctx := { ctx with
    constructorInfos := ctx.constructorInfos.insert
      (Tag.Builtin "List.nil") { arity := 0, memRep := MemRep.List .Nil }
  }

  let ctx := { ctx with
    constructorInfos := ctx.constructorInfos.insert
      (Tag.Builtin "List.cons") { arity := 2, memRep := MemRep.List .Cons }
  }

  let ctx := { ctx with
    constructorInfos := ctx.constructorInfos.insert
      (Tag.Builtin "Option.none") { arity := 0, memRep := MemRep.Maybe .None }
  }

  let ctx := { ctx with
    constructorInfos := ctx.constructorInfos.insert
      (Tag.Builtin "Option.some") { arity := 1, memRep := MemRep.Maybe .Some }
  }

  ctx

/-- Build a complete Nock program from compiled bindings -/
def buildProgram (bindings : Array (Lean.Name × Noun)) (mainExpr : Noun) : Noun :=
  if bindings.isEmpty then
    -- If no bindings, just return the main expression
    mainExpr
  else
    -- Create the subject (environment) containing all bindings
    let subject := bindings.foldl
      -- In Nock, we use op 8 (extend) to add bindings to the subject
      -- [8 [1 value] continuation]
      (fun subj (name, value) => opPush value subj)
      (atom 0)

    -- Compose the final Nock program by applying the main expression
    -- to the environment we built using Nock op 7 (compose)
    opSeq subject mainExpr

def compileExpr (env : Lean.Environment) (expr : Lean.Expr) : IO Noun := do
  -- let env ← Lean.mkEmptyEnvironment
  let ctx := CompilerCtx.fromEnv env
  -- let ctx := addNockPrelude ctx

  try
    -- Create an initial state
    let initialState := CompilerState.empty

    -- Execute the monad with proper unwrapping:
    let coreM := (((mkExpr expr).run ctx).run initialState).toIO
      {fileName := "", fileMap := default}
      {env}

    -- Return both the result and final state
    let ((noun, finalState), _) ← coreM

    -- Build a complete Nock program with all dependencies
    let program := buildProgram finalState.appendedBindings noun
    pure program
  catch e =>
    IO.println s!"Error compiling {expr}: {e}"
    pure 0

/-- Main entry point for compiling a declaration to Nock -/
def compileTerm (env : Lean.Environment) (declName : Lean.Name) : IO Noun := do
  let ctx := CompilerCtx.fromEnv env
  -- let ctx := addNockPrelude ctx

  try
    -- Create an initial state
    let initialState := CompilerState.empty

    -- Execute the monad with proper unwrapping:
    let coreM := (((mkDecl declName).run ctx).run initialState).toIO
      {fileName := "", fileMap := default}
      {env}

    -- Return both the result and final state
    let ((noun, finalState), _) ← coreM

    -- Build a complete Nock program with all dependencies
    let program := buildProgram finalState.appendedBindings noun
    pure program
  catch e =>
    IO.println s!"Error compiling {declName}: {e}"
    pure 0

/-- Main entry point for evaluating a compiled term -/
def evalTerm (env : Lean.Environment) (declName : Lean.Name) : IO (Option Noun) := do
  let noun ← compileTerm env declName
  -- Run the compiled term through the Nock interpreter
  let result := Leanur.Nock.Interpreter.tar (cell 0 noun)
  pure result

end Leanur.Compiler
