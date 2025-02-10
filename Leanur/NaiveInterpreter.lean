section

/- AST -/

abbrev Atom := Nat
inductive Noun
  | atom : Atom -> Noun
  | cell : Noun -> Noun -> Noun
deriving Repr, DecidableEq

instance : OfNat Noun a where
  ofNat := Noun.atom a

def Noun.toString : Noun -> String
  | .atom a => ToString.toString a
  | .cell a b => ToString.toString [a.toString, b.toString]

#eval Noun.toString (.cell 1 2)
#eval Noun.toString (.cell 1 (.cell 2 3))
#eval Noun.toString (.cell (.cell 1 4) (.cell 2 3))

-- -- TODO: needs to handle nested lists
-- def fromList : List Atom -> Noun
--   | [] => .atom 0
--   | [a] => .atom a
--   | a :: rest => .cell (.atom a) (fromList rest)

-- #eval fromList [1,2]
-- #eval fromList [1,2,3]

/- SYNTAX -/

declare_syntax_cat noun
syntax num : noun
syntax "[" num "]" : noun
syntax "[" num num "]" : noun
syntax "[" num num num+ "]" : noun

open Lean
macro_rules
  | `(noun| $n:num)
  | `(noun| [$n:num]) => `(Noun.atom `($n))
  | `(noun| [$n₁:num $n₂:num]) => `(Noun.cell `($n₁) `($n₂))
  -- | `(noun| [$n₁:num $n₂:num $n:num+]) => `(Noun.cell `($n₁) `($n₂))

-- /-- info: (Noun.atom 3) -/
-- #guard_msgs in
-- #check `(noun| 3)

-- open Noun

def wut : Noun -> Noun
  | .atom _ => .atom 0
  | .cell _ _ => .atom 1

#eval wut (.atom 2)

def lus : Noun -> Noun
  | .atom a => .atom (a + 1)
  | .cell a b => .cell a b

def tis : Noun -> Noun -> Noun
  | a, b => if a == b then .atom 0 else .atom 1

#eval tis (.atom 2) (.atom 2)
#eval tis (.atom 2) (.atom 3)
#eval tis (.cell 2 3) (.cell 2 3)
#eval tis (.cell 2 2) (.cell 2 3)

partial def fas : Noun -> Noun
  | .cell 1 a => a
  | .cell 2 (.cell a _) => a
  | .cell 3 (.cell _ b) => b
  | .cell (.atom a) b =>
    let a' := .atom (a / 2)
    if a % 2 == 0 then
      fas (.cell 2 (fas (.cell a' b)))
    else
      fas (.cell 3 (fas (.cell a' b)))
  | n => n

def fas' : Noun -> Option Noun
  | .cell 1 a => a
  | .cell 2 (.cell a _) => a
  | .cell 3 (.cell _ b) => b
  | .cell (.atom a) b =>

    none
  | _ => none

-- #eval fas (.cell 1 )

-- #check

def hax : Noun -> Noun
  | _ => sorry

def tar : Noun -> Noun
  | _ => sorry

end
