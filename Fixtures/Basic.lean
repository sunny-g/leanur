import Lean

namespace Fixtures.Basic

def const : Nat := 42

/-- Simple identity function -/
def id (x : Nat) : Nat := x

/-- Simple addition function -/
def add (x y : Nat) : Nat := x + y

/-- Constant function -/
def constant (x : Nat) : Nat := 42

/-- Simple constructor example -/
inductive SimpleData where
  | first : SimpleData
  | second : Nat → SimpleData
  | third : Nat → Nat → SimpleData

/-- Function using pattern matching -/
def matchExample (d : SimpleData) : Nat :=
  match d with
  | SimpleData.first => 0
  | SimpleData.second n => n
  | SimpleData.third n m => n + m

end Fixtures.Basic
