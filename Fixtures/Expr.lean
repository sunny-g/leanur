import Lean
-- import Batteries.Lean.Expr
import Leanur.Nock

namespace Fixtures.Expr

open Lean Meta
open Leanur.Nock

structure ExprFixture where
  jock : String
  expected : Noun
  expr : Expr := default

open DSL in
def ifElse : ExprFixture := {
  jock := "let a: @ = 3;if a == 3 { 72 } else { 17 }"
  expected := ⟦8 ⟦1 3⟧ 6 ⟦5 ⟦0 2⟧ 1 3⟧ ⟦1 72⟧ 1 17⟧
}

open DSL in
def letEdit : ExprFixture := {
  jock := "let a: ? = true;a = false;"
  expected := ⟦8 ⟦1 0⟧ 7 ⟦10 ⟦2 1 1⟧ 0 1⟧ 0 2⟧
  expr := .letE
    `a
    (.const `Bool [])
    (.const `Bool.true [])
    -- (Expr.letE `a (.const `Nat []) (.lit (.natVal 2)) (.bvar 0) true)
    (mkApp (.const ``MVarId.mk []) (.const `Bool.false []))
    -- (mkLocalDeclEx (.fvar {name:=`a}) `a )
    true
}

#eval ppExpr letEdit.expr

end Fixtures.Expr
