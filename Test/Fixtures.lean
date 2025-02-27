import Lean
import Leanur.Compiler

import Fixtures.Expr

/-!
  Test suite for the Leanur.Compiler module.

  This file tests the compilation of Lean4 programs to Nock. It compiles various
  expressions and programs and displays the resulting Nock code.
-/

namespace Test.Fixtures

open Lean
open Leanur.Compiler
open Leanur.Nock
open Fixtures.Expr

/-- Test descriptor for a compiler test -/
structure ProgramFixture where
  -- name : String
  declName : Name
  expr : Bool := false
  expected : Noun := default -- optional expected output for validation

/- Test cases for raw expressions -/
def testExprs : List (Name × ExprFixture) := [
  (`Fixtures.Expr.ifElse, Fixtures.Expr.ifElse),
  (`Fixtures.Expr.letEdit, Fixtures.Expr.letEdit),
]

/- Test cases for basic programs -/
def testPrograms : List ProgramFixture := [
  -- Basic.lean
  { declName := `Fixtures.Basic.const },
  -- { declName := `Fixtures.Basic.id },
  -- { declName := `Fixtures.Basic.add },
  -- { declName := `Fixtures.Basic.constant },
  -- { declName := `Fixtures.Basic.SimpleData.first },
  -- { declName := `Fixtures.Basic.SimpleData.second },
  -- { declName := `Fixtures.Basic.SimpleData.third },
  -- { declName := `Fixtures.Basic.matchExample },
  -- Recursion.lean
  -- { declName := `Fixtures.Recursion.fact },
  -- { declName := `Fixtures.Recursion.fib },
  -- { declName := `Fixtures.Recursion.even },
  -- { declName := `Fixtures.Recursion.odd },
]

private def test (name : Name) (expected : Noun) (actual : IO Noun) : IO Unit := do
  IO.println s!"==== Testing {name} ===="
  let actual ← actual

  IO.println "Compiled Nock code:"
  IO.println (toString actual)

  if actual == expected then
    IO.println "✅ Output matches expected"
  else
    IO.println "❌ Output doesn't match expected:"
    IO.println (toString expected)

  IO.println "==== End Test ====\n"

/-- Run all compiler tests -/
def run : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)

  -- Get the environment with all imported modules
  let env ← Lean.importModules
    #[`Fixtures.Expr
    , `Fixtures.Basic
    , `Fixtures.Recursion
    ]
    {}

  -- Run tests
  for (name, fixture) in testExprs do
    test name fixture.expected do {
      IO.println s!"Jock expression: {fixture.jock}";
      IO.println s!"Lean expression: {fixture.expr}";
      compileExpr env fixture.expr
    }
  for prog in testPrograms do
    test prog.declName prog.expected do
      compileTerm env prog.declName

end Test.Fixtures

/-- Main entry point for compiler tests -/
def main : IO Unit := do
  IO.println "Running Leanur Compiler Tests"
  IO.println "==============================\n"

  Test.Fixtures.run
