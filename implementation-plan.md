# Leanur Implementation Plan: Compiling Lean4 to Nock

This document outlines the implementation plan for the Leanur project, which aims to compile Lean4 programs to Nock, a minimalist combinator calculus.

## 1. Core Data Structures

### Target Language (Nock)

We already have a solid implementation of Nock in `Leanur.Nock.lean`, which defines:

```lean
namespace Leanur.Nock
  abbrev Atom := Nat  -- Base atomic values as natural numbers

  inductive Noun  -- The core Nock data type
    | atom : Atom -> Noun
    | cell : Noun -> Noun -> Noun
```

These are sufficient for representing all Nock data.

### Source Language (Lean4 LCNF)

For compilation, we need to handle Lean4's LCNF (Low-level Continuation-passing Normal Form), which is an intermediate representation used by the Lean4 compiler. The key types from Lean's LCNF include:

1. **Decl**: Top-level declarations (functions, constants)
2. **FunDecl**: Function declarations with parameters and body
3. **Code**: Represents code blocks (let bindings, function calls, pattern matching)
4. **LetValue**: Right-hand sides of let bindings (constants, function calls, projections)
5. **LetDecl**: A binding (variable and its value)
6. **Alt**: Branches in pattern matching

## 2. Compilation Monad

We'll define a monadic structure similar to Yatima's `CodeGenM` for our compilation process:

```lean
structure CompilerCtx where
  env : Lean.Environment        -- Lean environment containing declarations
  overrides : Lean.NameMap Override  -- Special handling for built-in ops
  functionInfos : HashMap FunctionId FunctionInfo  -- Function metadata
  constructorInfos : HashMap Tag ConstructorInfo   -- Constructor metadata
  tempVarMap : HashMap Int TempRef  -- Manages temporary variable stack
  tempVarsNum : Int                 -- Counter for temporary variables
  stackHeight : Int                 -- Current stack height for Nock compilation

structure CompilerState where
  appendedBindings : Array (Lean.Name × Noun)  -- Compiled bindings
  visited : Lean.NameSet                       -- Visited declarations
  replaced : Lean.NameMap Lean.Name            -- Renamed declarations

abbrev CompilerM := ReaderT CompilerCtx (StateRefT CompilerState IO)
```

## 3. Key Components to Implement

### 3.1 Core Compilation Functions

1. **compileDecl**: Main entry point for compiling a declaration
   ```lean
   def compileDecl (declName : Lean.Name) : CompilerM Noun
   ```

2. **compile**: Recursive function to convert LCNF code to Nock
   ```lean
   def compile : Code → CompilerM (Noun)
   ```

3. **mkLetValue**: Handle let bindings (constants, function calls, projections)
   ```lean
   def mkLetValue : LetValue → CompilerM Noun
   ```

4. **mkFunDecl**: Compile function declarations
   ```lean
   def mkFunDecl : FunDecl → CompilerM Noun
   ```

5. **mkCase**: Compile pattern matching
   ```lean
   def mkCase : Cases → CompilerM Noun
   ```

### 3.2 Stack Management Functions

The heart of the Nock compilation strategy is stack-based since Nock has no built-in variable binding:

1. **withTemp**: Push a value onto the stack for temporary use
   ```lean
   def withTemp : Noun → (TempRef → CompilerM Noun) → CompilerM Noun
   ```

2. **withTempVar**: Push and track a temporary variable
   ```lean
   def withTempVar : Noun → (TempRef → CompilerM Noun) → CompilerM Noun
   ```

3. **tempRefPath**: Calculate the path to a temporary reference
   ```lean
   def tempRefPath : TempRef → CompilerM Path
   ```

### 3.3 Function Handling and Closure Support

1. **Function Representation**: Represent closures as structured data with fields:
   - FunCode: The function's code
   - ArgsTuple: The arguments tuple
   - ClosureRemainingArgsNum: Remaining argument count for partial application
   - FunctionsLibrary: Available functions

2. **callFunWithArgs**: Function call mechanism
   ```lean
   def callFunWithArgs : FunctionId → List Noun → CompilerM Noun
   ```

3. **curryClosure**: Support for partial application
   ```lean
   def curryClosure : Noun → List Noun → Noun → CompilerM Noun
   ```

### 3.4 Algebraic Data Type Support

1. **Constructor Representation**: Encode constructors as Nock cells with tags
   ```lean
   def mkConstructor : Tag → List Noun → CompilerM Noun
   ```

2. **Memory Representation Selection**: Choose appropriate representation styles:
   - Standard constructors
   - Tuples (single constructor types)
   - Specialized representations for common types (List, Option, etc.)

### 3.5 Overrides for Built-in Operations

Similar to Yatima's approach, we'll need overrides for basic operations:

```lean
def addNockPrelude (env : CompilerEnv) : CompilerEnv :=
  -- Add standard overrides for primitive operations
  let env := { env with
    overrides := env.overrides.insert `Nat.add (.expr <special implementation>) }
```

## 4. Implementation Phases

### Phase 1: Basic Infrastructure
- [x] Define Nock interpreter (already done)
- [ ] Implement core monad and data structures
- [ ] Create basic compiler infrastructure

### Phase 2: Core Feature Support
- [ ] Implement simple expressions (constants, literals)
- [ ] Support for basic function calls
- [ ] Add let binding support

### Phase 3: Advanced Features
- [ ] Implement pattern matching (algebraic data types)
- [ ] Add support for closures and currying
- [ ] Handle recursive functions

### Phase 4: Optimizations and Standard Library
- [ ] Add specialized representations for common types
- [ ] Implement standard library functions
- [ ] Add optimizations for better code generation

## 5. Understanding the Compilation Process

### 5.1 What is LCNF?

Low-level Continuation-passing Normal Form (LCNF) is Lean4's intermediate representation where:
- Functions are in continuation-passing style
- All intermediate values are named
- Control flow is explicit
- Pattern matching is broken down into simpler constructs

### 5.2 Compilation Strategy

1. **Stack-Based Model**: Nock uses a subject-based model where all operations act on a "subject" (like a stack or environment)

2. **Environment Building**: The compiler constructs a subject containing:
   - Function definitions
   - Argument values
   - Temporary values

3. **Function Calls**: Function calls in Nock require:
   - Locating the function code
   - Building an environment with arguments
   - Applying the Nock call operator

4. **Variable Access**: Variables are accessed by path (location in the subject)

5. **Pattern Matching**: Implemented as a series of Nock equality tests and conditionals

## 6. Critical Functions Explained

### withTemp
This function is crucial as it manages the stack-based nature of Nock. It:
1. Pushes a value onto the stack
2. Increases the stack height
3. Compiles the body with the updated context
4. Returns a Nock expression that uses Nock's Push operator (8)

### compile
The recursive compilation function translates Lean's LCNF to Nock by:
1. Pattern matching on the LCNF code structure
2. Dispatching to specialized handlers for each construct
3. Composing the results into valid Nock expressions

### callFunWithArgs
Implements the function calling convention by:
1. Collecting and packaging arguments
2. Locating the function in the library
3. Building a new environment with the arguments
4. Using Nock's call operator (9) to invoke the function

## 7. Example: Compiling a Simple Function

For a function like:
```lean
def add (x y : Nat) : Nat := x + y
```

The compilation process will:

1. Translate to LCNF (handled by Lean)
2. Compile the function body (addition)
3. Create a closure representation
4. Generate Nock code for the function call mechanism
5. Produce a complete Nock program that can be interpreted

This implementation plan provides the foundation for building a complete Lean4 to Nock compiler, drawing on the techniques used in both Juvix and Yatima.
