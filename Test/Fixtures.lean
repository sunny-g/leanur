import Lean
import Leanur.Compiler

/-!
  Test suite for the Leanur.Compiler module.

  This file tests the compilation of Lean4 programs to Nock. It compiles various
  expressions and programs and displays the resulting Nock code.
-/

namespace Test.Compiler.Fixtures

open Lean
open Leanur.Compiler
open Leanur.Nock

/-- Test descriptor for a compiler test -/
structure TestCase where
  -- name : String
  declName : Name
  expr : Bool := false
  expected : Option Noun := none -- optional expected output for validation

/- Test cases for raw expressions -/
open DSL in
def testExpressions : List TestCase := [
  { declName := `Fixtures.Expr.letEdit,
    expr := true,
    expected := ⟦8 ⟦1 0⟧ 7 ⟦10 ⟦2 1 1⟧ 0 1⟧ 0 2⟧ }
]

/- Test cases for basic programs -/
open DSL in
def testPrograms : List TestCase := [
  -- Basic.lean
  { declName := `Fixtures.Basic.const },
  { declName := `Fixtures.Basic.id },
  { declName := `Fixtures.Basic.add },
  { declName := `Fixtures.Basic.constant },
  { declName := `Fixtures.Basic.SimpleData.first },
  { declName := `Fixtures.Basic.SimpleData.second },
  { declName := `Fixtures.Basic.SimpleData.third },
  { declName := `Fixtures.Basic.matchExample },
  -- Recursion.lean
  { declName := `Fixtures.Recursion.fact },
  { declName := `Fixtures.Recursion.fib },
  { declName := `Fixtures.Recursion.even },
  { declName := `Fixtures.Recursion.odd },
  -- Jock/*.lean
  -- { declName := `Fixtures.Jock.Dec.dec,
  --   expected := ⟦8 ⟦8 ⟦1 0⟧ ⟦1 8 ⟦1 0⟧ 8 ⟦1 6 ⟦5 ⟦0 30⟧ 4 0 6⟧ ⟦0 6⟧ 7 ⟦10 ⟦6 4 0 6⟧ 0 1⟧ 9 2 0 1⟧ 9 2 0 1⟧ 0 1⟧ 8 ⟦0 2⟧ 9 2 10 ⟦6 7 ⟦0 3⟧ 1 5⟧ 0 2⟧ },
]

/-- Run a single compiler test case -/
def runTest (tc : TestCase) (env : Environment) : IO Unit := do
  IO.println s!"==== Testing {tc.declName} ===="

  -- Compile the declaration to Nock
  let noun ← compileTerm env tc.declName

  -- Pretty print the Nock code
  let nockStr := toString noun

  -- Display the compiled Nock code
  IO.println "Compiled Nock code:"
  IO.println nockStr

  -- If we have expected output, validate it
  match tc.expected with
  | none => pure ()
  | some expected =>
    if noun == expected then
      IO.println "✅ Output matches expected"
    else
      IO.println "❌ Output doesn't match expected:"
      IO.println (toString expected)

  IO.println "==== End Test ===="
  IO.println ""

/-- Run all compiler tests -/
def runAllTests : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)

  -- Get the environment with all imported modules
  let env ← Lean.importModules
    #[`Fixtures.Expr
    , `Fixtures.Basic
    , `Fixtures.Recursion
    -- , `Fixtures.Jock.Dec
    ]
    {}

  -- let envHeader := env.header
  -- let idx := envHeader.moduleNames.idxOf `Fixtures.Basic
  -- let imports := envHeader.moduleData.get! idx |>.constNames
  -- IO.println s!"loaded imports {imports}"

  -- Run tests
  for test in testExpressions do runTest test env
  -- for test in testPrograms do runTest test env

end Test.Compiler.Fixtures

/-- Main entry point for compiler tests -/
def main : IO Unit := do
  IO.println "Running Leanur Compiler Tests"
  IO.println "=============================="
  IO.println ""

  Test.Compiler.Fixtures.runAllTests
