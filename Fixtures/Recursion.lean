import Lean

namespace Fixtures.Recursion

/-- Recursive factorial function -/
def fact (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n+1 => (n+1) * fact n

/-- Recursive fibonacci function -/
def fib (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n+2 => fib (n+1) + fib n

/- Mutually recursive even/odd functions -/
mutual
  def even (n : Nat) : Bool :=
    match n with
    | 0 => true
    | n+1 => odd n

  def odd (n : Nat) : Bool :=
    match n with
    | 0 => false
    | n+1 => even n
end

end Fixtures.Recursion
