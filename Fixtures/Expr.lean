import Lean
-- import Batteries.Lean.Expr

namespace Fixtures.Expr

open Lean Meta

/-
let a : Bool := false;
a := true;
-/
def letEdit : Expr := .letE
  `a
  (.const `Bool [])
  (.const `Bool.false [])
  -- (Expr.letE `a (.const `Nat []) (.lit (.natVal 2)) (.bvar 0) true)
  (mkApp (.const ``MVarId.mk []) (.const `Bool.true []))
  -- (mkLocalDeclEx (.fvar {name:=`a}) `a )
  true

#eval ppExpr letEdit
-- #eval toExpr (a := 2)

end Fixtures.Expr
