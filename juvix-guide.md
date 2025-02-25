Compiling Juvix to Nock: An Intermediate Guide

Juvix is a functional programming language with advanced features, and "Nockma"
is its backend that compiles a Juvix Tree intermediate representation into Nock,
a minimalist combinator calculus. This tutorial breaks down the key data
structures and compilation techniques used in this process.

1. The Data Structures

Nock Language (Target)

Nock is represented using these core data structures:

```haskell
data Term a
  = TermAtom (Atom a)    -- Atomic values
  | TermCell (Cell a)    -- Cell pairs: [a b]

data Cell a = Cell'
  { _cellLeft :: Term a,  -- Left component
    _cellRight :: Term a, -- Right component
    _cellInfo :: CellInfo a -- Metadata
  }

data Atom a = Atom
  { _atom :: a,           -- The actual value
    _atomInfo :: AtomInfo  -- Metadata
  }
```

These primitives are used to encode a set of operations (represented by NockOp):

```haskell
data NockOp
  = OpAddress   -- @ - Fetch data at a path
  | OpQuote     -- Quote literal data
  | OpApply     -- Apply a function
  | OpIsCell    -- Test if a value is a cell
  | OpInc       -- Increment
  | OpEq        -- Equality test
  | OpIf        -- Conditional branching
  | OpSequence  -- Sequence operations
  | OpPush      -- Push onto subject stack
  | OpCall      -- Function call
  | OpReplace   -- Modify the subject
  | OpHint      -- Add runtime hints
  | OpScry      -- External data lookup
```

Juvix Tree (Source)

Juvix Tree is the intermediate representation that gets compiled to Nock:

```haskell
data Node
  = Binop NodeBinop           -- Binary operations
  | Unop NodeUnop             -- Unary operations
  | Constant NodeConstant     -- Constant values
  | MemRef NodeMemRef         -- Memory references
  | AllocConstr NodeAllocConstr -- Create data structures
  | AllocClosure NodeAllocClosure -- Create function closures
  | ExtendClosure NodeExtendClosure -- Add arguments to closures
  | Call NodeCall             -- Function calls
  | Branch NodeBranch         -- Conditional branching
  | Case NodeCase             -- Pattern matching
  | Save NodeSave             -- Local bindings
  -- plus other specialized node types
```

This represents a rich functional language with features like closures, algebraic
  data types, and pattern matching.

2. Compilation Process

The compilation entry point is fromTreeTable, which takes a Juvix Tree InfoTable
(containing all functions and their implementations) and compiles everything to
Nock.

Function Compilation Strategy

The core of Juvix-to-Nock compilation is in the compile function, which
recursively translates Juvix Tree Node structures into Nock Term structures:

```haskell
compile :: Node -> Sem r (Term Natural)
compile = \case
  Tree.Binop b -> goBinop b
  Tree.Unop b -> goUnop b
  Tree.Constant c -> return (goConstant (c ^. Tree.nodeConstant))
  Tree.MemRef c -> goMemRef (c ^. Tree.nodeMemRef)
  Tree.AllocConstr c -> goAllocConstr c
  Tree.AllocClosure c -> goAllocClosure c
  Tree.ExtendClosure c -> goExtendClosure c
  Tree.Call c -> goCall c
  Tree.Branch b -> goBranch b
  Tree.Case c -> goCase c
  Tree.Save s -> goSave s
  -- plus handlers for other node types
```

Key Compilation Techniques

1. Stack-Based Compilation: The heart of the Nock compilation uses a stack-based
approach. Values are pushed onto a "subject stack" and later referenced by their
position. This stack manipulation is essential since Nock has no built-in
variable binding mechanism.
2. Temporary Variables: The compiler manages a stack of temporary values using
functions like withTemp, withTempVar, and addressTempRef. This is crucial for
implementing let-bindings and avoiding code duplication:

```haskell
withTemp :: Term Natural -> (TempRef -> Sem r (Term Natural)) -> Sem r (Term
Natural)
withTemp value f = do
  stackHeight <- asks (^. compilerStackHeight)
  body' <- local (over compilerStackHeight (+ 1)) $ f (TempRef stackHeight)
  return $ OpPush # value # body'
```
3. Closures as Structured Data: Closures in Nock are represented as structured
data with specific fields:
  - FunCode: The function's code
  - ArgsTuple: The arguments tuple
  - ClosureRemainingArgsNum: Number of arguments remaining
  - FunctionsLibrary: A library of available functions
  - AnomaLibrary: Standard library functions
4. Pattern Matching Compilation: The goCase function translates pattern matching
to a series of Nock equality tests and conditional branches.

Function Calling Convention

Function calls are compiled using a special calling convention:

1. Arguments are collected and formatted as a tuple
2. The function code is located in the functions library
3. The arguments are added to the environment
4. A Nock OpCall operation applies the function to its arguments

```haskell
callFunWithArgs :: FunctionId -> [Term Natural] -> Sem r (Term Natural)
callFunWithArgs fun args = do
  newSubject <- replaceArgs args
  fpath <- getFunctionPath fun
  fname <- getFunctionName fun
  let p' = fpath ++ closurePath FunCode
  return (opCall ("callFun-" <> fname) p' newSubject)
```

Currying and Partial Application

Juvix supports currying through the curryClosure function, which creates a new
closure with some arguments pre-applied:

```haskell
curryClosure :: Term Natural -> [Term Natural] -> Term Natural -> Sem r (Term
Natural)
curryClosure f args newArity = do
  -- Create a new closure with some arguments pre-applied
  let args' = (foldTerms (nonEmpty' $ map (\x -> (OpQuote # OpQuote) # x) args
                <> [OpQuote # OpAddress # closurePath ArgsTuple]))
  -- Return a new closure with updated fields
  return . makeClosure $ \case
    FunCode -> (OpQuote # OpCall) # ... # f
    ClosureRemainingArgsNum -> newArity
    -- other fields...
```

Algebraic Data Types

Algebraic data types are compiled into cell structures with tags:

1. Tag-based encoding: Constructor data is encoded as `[tag args]` where tag
identifies the constructor and args is the list of arguments.
2. Memory representation: Different memory representations are chosen based on
the data type:
  - `NockmaMemRepConstr`: General constructors
  - `NockmaMemRepTuple`: Single-constructor types (like tuples)
  - `NockmaMemRepList`: List-like types with nil/cons constructors
  - `NockmaMemRepMaybe`: Maybe-like types with nothing/just constructors

3. Optimization Techniques

Several optimizations are employed in the compilation process:

1. Avoiding Code Duplication: The withTemp pattern ensures compiled expressions
aren't duplicated, preventing exponential code growth.
2. Specialized Memory Representations: Lists and Maybe types get specialized
memory representations that are more efficient.
3. Path Optimization: Nock paths (used to access data) are optimized to reduce
the number of operations.
4. Quote and Evaluation Control: The compiler carefully manages what is quoted
(literal) vs. what is evaluated, controlling evaluation order.

4. Example: Compiling a Simple Function

To illustrate the translation process, let's trace how a simple Juvix function
might be compiled:

For a function like:
let add x y = x + y

1. The Juvix Tree representation would be something like:
```haskell
AllocClosure {
  funSymbol = "add",
  args = []  -- No arguments applied yet
}
```
2. When this closure is applied to arguments, it becomes:
```haskell
Call {
  type = CallFun "add",
  args = [x, y]
}
```
3. Compiling this would:
  - Compile the arguments x and y
  - Create an arguments tuple with them
  - Look up the function in the functions library
  - Generate a Nock term that calls the function with the arguments

Conclusion

The Juvix to Nock compiler translates a rich functional language into a minimal
combinator calculus by:

1. Encoding high-level features (algebraic data types, pattern matching,
closures) using simple Nock pairs and atoms
2. Managing a compilation stack to handle temporary values and closures
3. Utilizing specialized memory representations for common data structures
4. Carefully controlling evaluation order through quotation

This translation demonstrates how a minimal target language can still support
rich programming features when coupled with a sophisticated compilation strategy.
