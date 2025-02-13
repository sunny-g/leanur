import Lean

section AST

abbrev Atom := Nat
inductive Noun
  | atom : Atom -> Noun
  | cell : Noun -> Noun -> Noun
deriving Repr, BEq, DecidableEq, Hashable

section Compat

instance : OfNat Noun a where ofNat := Noun.atom a

-- set_option diagnostics true
class ToNoun (α : Type _) where toNoun : α -> Noun
export ToNoun (toNoun)

instance : ToNoun Atom where toNoun := .atom
instance : ToNoun Noun := ⟨id⟩
-- private def any2Noun [ToNoun α] [ToNoun (List α)] : List α -> Noun
--   | [a] => toNoun a
--   | [a, b] => .cell (toNoun a) (toNoun b)
--   | a :: b => .cell (toNoun a) (any2Noun (b.map toNoun))
--   | []  => .atom 1
-- instance [ToNoun α] : ToNoun (List α) where toNoun ns := any2Noun (ns.map toNoun)

private def al2Noun : List Atom -> Noun
  | [a] => toNoun a
  | [a, b] => .cell (toNoun a) (toNoun b)
  | a :: b => .cell (toNoun a) (al2Noun b)
  | [] => toNoun 0
instance : ToNoun (List Atom) where toNoun := al2Noun

private def nl2Noun : List Noun -> Noun
   | [a] => a
   | [a, b] => .cell a b
   | a :: b => .cell a (nl2Noun b)
   | []  => toNoun 0
instance [ToNoun α] : ToNoun (List α) where toNoun ns := nl2Noun (ns.map toNoun)

#eval ToNoun.toNoun [1]
#eval ToNoun.toNoun [1, 2]
#eval ToNoun.toNoun [[1, 2]]
#eval ToNoun.toNoun [1, 2, 3]
#eval ToNoun.toNoun [[1, 2], 3]
#eval ToNoun.toNoun [1, [2, 3]]
#eval ToNoun.toNoun [1, 2, 3, 4]
#eval ToNoun.toNoun [[1, 2], [3, 4]]

open Std Format in
def Noun.toFormat : Noun -> Format
  | .atom a => format a
  | .cell a b => format "⟦" ++ a.toFormat ++ " " ++ b.toFormat ++ "⟧"

def Noun.toString : Noun -> String :=
  ToString.toString ∘ Noun.toFormat

instance : Std.ToFormat Noun where format := Noun.toFormat
instance : ToString Noun where toString := Noun.toString

#eval Noun.toString (.atom 2)
#eval Noun.toString (.cell 1 2)
#eval Noun.toString (.cell 1 (.cell 2 3))
#eval Noun.toString (.cell (.cell 1 2) (.cell 3 4))



-- -- TODO: needs to handle nested lists
-- def fromList : List Atom -> Noun
--   | [] => .atom 0
--   | [a] => .atom a
--   | a :: rest => .cell (.atom a) (fromList rest)

-- #eval fromList [1,2]
-- #eval fromList [1,2,3]

end Compat

end AST

namespace DSL

open Lean

declare_syntax_cat noun
syntax num+           : noun
syntax "⟦" noun+ "⟧"  : noun
syntax noun           : term

instance : Coe (TSyntax `noun) (TSyntax `term) where coe n := ⟨n.raw⟩

macro_rules
  | `(noun| $nums:num* $num:num) => do
    let mut acc : TSyntax `term <- `(Noun.atom $num)
    for num in nums.reverse do acc <- `(Noun.cell $num $acc)
    return acc
  | `(noun| ⟦$nouns:noun* $noun:noun⟧) => do
    let mut acc : TSyntax `term <- `($noun)
    for noun in nouns.reverse do acc <- `(Noun.cell $noun $acc)
    return acc
  | `($noun:noun) => `($noun)

#reduce ⟦1⟧ == Noun.atom 1
#reduce ⟦1 2⟧ == Noun.cell 1 2
#reduce ⟦⟦1 2⟧⟧ == Noun.cell 1 2
#reduce ⟦1 2 3⟧ == Noun.cell 1 (Noun.cell 2 3)
#reduce ⟦⟦1 2⟧ 3⟧ == Noun.cell (Noun.cell 1 2) 3
#reduce ⟦1 ⟦2 3⟧⟧ == Noun.cell 1 (Noun.cell 2 3)
#reduce ⟦1 2 3 4⟧ == Noun.cell 1 (Noun.cell 2 (Noun.cell 3 4))
#reduce ⟦⟦1 2⟧ ⟦3 4⟧⟧ == Noun.cell (Noun.cell 1 2) (Noun.cell 3 4)

end DSL

namespace Interpreter

def wut : Noun -> Noun
  | .atom _ => .atom 0
  | .cell _ _ => .atom 1

#eval wut (.atom 2) == 0
#eval wut (.cell 1 2) == 1

def lus : Noun -> Noun
  | .atom a => .atom (a + 1)
  | .cell a b => .cell a b

def tis : Noun -> Noun -> Noun
  | a, b => if a == b then .atom 0 else .atom 1

#eval tis (.atom 2) (.atom 2) == 0
#eval tis (.atom 2) (.atom 3) == 1
#eval tis (.cell 2 3) (.cell 2 3) == 0
#eval tis (.cell 2 2) (.cell 2 3) == 1

private partial def fas' : Noun -> Noun
  | .cell 1 a => a
  | .cell 2 (.cell a _) => a
  | .cell 3 (.cell _ b) => b
  | .cell (.atom a) b =>
    let a' := .atom (a / 2)
    if a % 2 == 0 then
      fas' (.cell 2 (fas' (.cell a' b)))
    else
      fas' (.cell 3 (fas' (.cell a' b)))
  | n => n

def fas : Noun -> Option Noun
  | .cell 1 a => a
  | .cell 2 (.cell a _) => a
  | .cell 3 (.cell _ b) => b
  | .cell (.atom a) b =>

    none
  | _ => none

-- #eval fas (.cell 1 )

def hax : Noun -> Noun
  | _ => sorry

def tar : Noun -> Noun
  | _ => sorry

def eval : Noun -> Option Noun
  | _ => sorry

end Interpreter
