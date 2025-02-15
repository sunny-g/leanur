section AST

abbrev Atom := Nat
inductive Noun
  | atom : Atom -> Noun
  | cell : Noun -> Noun -> Noun
deriving BEq, DecidableEq, Hashable

section Compat

instance : Coe Nat Atom where coe a := a
instance : Coe Atom Nat where coe a := a
instance : Coe Atom Noun where coe a := .atom a

-- instance : SizeOf Noun where
--   sizeOf n := match n with
--     | .atom a => a
--     | .cell (.atom a) b =>

instance : OfNat Noun n where ofNat := .atom n

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

def Noun.toString : Noun -> String := ToString.toString ∘ Noun.toFormat

instance : Std.ToFormat Noun where format := Noun.toFormat
instance : ToString Noun where toString := Noun.toString

#eval Noun.toString 2
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
scoped syntax num           : noun
scoped syntax "⟦" noun+ "⟧" : noun
scoped syntax noun          : term

instance : Coe (TSyntax `noun) (TSyntax `term) where coe n := ⟨n.raw⟩

macro_rules
  | `(noun| $num:num) => `(Noun.atom $num)
  | `(noun| ⟦$nouns:noun* $noun:noun⟧) => do
    let mut acc : TSyntax `term <- `($noun)
    for noun in nouns.reverse do acc <- `(Noun.cell $noun $acc)
    return acc
  | `(term| $noun:noun) => `(noun| $noun)

#eval ⟦1⟧ == .atom 1
#eval ⟦1 2⟧ == .cell 1 2
#eval ⟦⟦1 2⟧⟧ == .cell 1 2
#eval ⟦1 2 3⟧ == .cell 1 (.cell 2 3)
#eval ⟦⟦1 2⟧ 3⟧ == .cell (.cell 1 2) 3
#eval ⟦⟦1 2⟧ 3 4⟧ == .cell (.cell 1 2) (.cell 3 4)
#eval ⟦1 ⟦2 3⟧⟧ == .cell 1 (.cell 2 3)
#eval ⟦1 2 ⟦3 4⟧⟧ == .cell 1 (.cell 2 (.cell 3 4))
#eval ⟦1 2 3 4⟧ == .cell 1 (.cell 2 (.cell 3 4))
#eval ⟦⟦1 2⟧ ⟦3 4⟧⟧ == .cell (.cell 1 2) (.cell 3 4)

end DSL

namespace Interpreter

open Noun

/- ?, cell or atom -/
def wut : Noun -> Noun
  | atom _ => 0
  | cell _ _ => 1
scoped prefix:50 "?" => wut

open DSL in #eval (?⟦1⟧) == ⟦0⟧
open DSL in #eval (?⟦1 2⟧) == ⟦1⟧

/- +, increment -/
def lus : Noun -> Noun
  | atom a => atom (a + 1)
  | cell a b => cell a b
scoped prefix:50 "+" => lus

open DSL in #eval (+⟦1⟧) == ⟦2⟧
open DSL in #eval (+⟦1 2⟧) == ⟦1 2⟧

/- =, equality -/
def tis : Noun -> Option Noun
  | cell a b => if a == b then some 0 else some 1
  | _ => none
scoped prefix:50 "=" => tis

open DSL in #eval (=⟦1⟧) == none
open DSL in #eval (=⟦1 2⟧) == ⟦1⟧
open DSL in #eval (=⟦2 2⟧) == ⟦0⟧
open DSL in #eval (=⟦⟦2 2⟧ ⟦2 3⟧⟧) == ⟦1⟧
open DSL in #eval (=⟦⟦2 3⟧ ⟦2 3⟧⟧) == ⟦0⟧

/- /, slot (tree addressing operator) -/
def fas : Noun -> Option Noun
  | cell 0 _ => none
  | cell 1 a => a
  | cell 2 (cell a _) => a
  | cell 3 (cell _ b) => b
  -- | cell (atom a) b =>
  -- using structural recursion? instead
  | cell (atom (Nat.succ a)) b =>
    match (fas (cell (atom ((a + 1) / 2)) b)) with
      | some (cell b c) => if (a + 1) % 2 == 0 then some b else some c
      | _ => none
  | _ => none
scoped prefix:50 "/" => fas

/-
     1
  2     3
4  5  6  7
       14 15
-/
open DSL in #eval (/⟦1 ⟦⟦4 5⟧ ⟦6 14 15⟧⟧⟧) == ⟦⟦4 5⟧ ⟦6 14 15⟧⟧
open DSL in #eval (/⟦2 ⟦⟦4 5⟧ ⟦6 14 15⟧⟧⟧) == ⟦4 5⟧
open DSL in #eval (/⟦3 ⟦⟦4 5⟧ ⟦6 14 15⟧⟧⟧) == ⟦6 14 15⟧
open DSL in #eval (/⟦4 ⟦⟦4 5⟧ ⟦6 14 15⟧⟧⟧) == ⟦4⟧
open DSL in #eval (/⟦5 ⟦⟦4 5⟧ ⟦6 14 15⟧⟧⟧) == ⟦5⟧
open DSL in #eval (/⟦6 ⟦⟦4 5⟧ ⟦6 14 15⟧⟧⟧) == ⟦6⟧
open DSL in #eval (/⟦7 ⟦⟦4 5⟧ ⟦6 14 15⟧⟧⟧) == ⟦14 15⟧
open DSL in #eval (/⟦8 ⟦⟦4 5⟧ ⟦6 14 15⟧⟧⟧) == none
--
open DSL in #eval (/⟦13 ⟦⟦4 5⟧ ⟦6 14 15⟧⟧⟧) == none
open DSL in #eval (/⟦14 ⟦⟦4 5⟧ ⟦6 14 15⟧⟧⟧) == ⟦14⟧

/- #, edit (replaces part of a noun with another) -/
partial def hax : Noun -> Option Noun
  | cell 1 (cell a _) => a
  -- | cell (atom (Nat.succ a)) (cell b c) => match (/(cell (atom (a)) c)) with
  --   | some d => if (a + 1) % 2 == 0
  --     then hax (cell (atom ((a + 1) / 2)) (cell (cell b d) c))
  --     else hax (cell (atom ((a) / 2)) (cell (cell d b) c))
  --   | _ => none
  | cell (atom (Nat.succ a)) (cell b c) => if (a + 1) % 2 == 0
    then (/(cell (atom (a + 2)) c)).bind
      fun d => hax (cell (atom ((a + 1) / 2)) (cell (cell b d) c))
    else (/(cell (atom a) c)).bind
      fun d => hax (cell (atom ((a) / 2)) (cell (cell d b) c))
  | _ => none
scoped prefix:50 "#" => hax

/-
  22  33

-/
open DSL in #eval (#⟦2 11 ⟦22 33⟧⟧) == ⟦11 33⟧
open DSL in #eval (#⟦3 11 ⟦22 11⟧⟧) == ⟦22 11⟧

open DSL in #eval (#⟦2 11 ⟦⟦22 33⟧ 44⟧⟧) == ⟦11 44⟧
open DSL in #eval (#⟦3 11 ⟦⟦22 33⟧ 44⟧⟧) == ⟦⟦22 33⟧ 11⟧
open DSL in #eval (#⟦4 11 ⟦⟦22 33⟧ 44⟧⟧) == ⟦⟦11 33⟧ 44⟧
open DSL in #eval (#⟦5 11 ⟦⟦22 33⟧ 44⟧⟧) == ⟦⟦22 11⟧ 44⟧

/-
  22  33
     44 55
-/
open DSL in #eval (#⟦1 ⟦123 456⟧ ⟦22 33 44 55⟧⟧) == ⟦123 456⟧
open DSL in #eval (#⟦2 ⟦123 456⟧ ⟦22 33 44 55⟧⟧) == ⟦⟦123 456⟧ 33 44 55⟧
open DSL in #eval (#⟦3 ⟦123 456⟧ ⟦22 33 44 55⟧⟧) == ⟦22 123 456⟧
open DSL in #eval (#⟦4 ⟦123 456⟧ ⟦22 33 44 55⟧⟧)
open DSL in #eval (#⟦5 ⟦123 456⟧ ⟦22 33 44 55⟧⟧)
open DSL in #eval (#⟦6 ⟦123 456⟧ ⟦22 33 44 55⟧⟧) == ⟦22 ⟦⟦123 456⟧ ⟦44 55⟧⟧⟧
open DSL in #eval (#⟦7 ⟦123 456⟧ ⟦22 33 44 55⟧⟧) == ⟦22 33 ⟦123 456⟧⟧
open DSL in #eval (#⟦8 ⟦123 456⟧ ⟦22 33 44 55⟧⟧)
--
open DSL in #eval (#⟦13 ⟦123 456⟧ ⟦22 33 44 55⟧⟧)
open DSL in #eval (#⟦14 ⟦123 456⟧ ⟦22 33 44 55⟧⟧) == ⟦22 ⟦33 ⟦⟦123 456⟧ 55⟧⟧⟧
open DSL in #eval (#⟦15 ⟦123 456⟧ ⟦22 33 44 55⟧⟧) == ⟦22 ⟦33 ⟦44 ⟦123 456⟧⟧⟧⟧

/- *, eval -/
partial def tar : Noun -> Option Noun
  /- core -/
  /-  -/
  | cell a (cell (cell b c) d) =>
    (tar (cell a (cell b c))).bind fun abc =>
      (tar (cell a d)).bind fun ad =>
        cell abc ad
  /- 0 -/
  | cell a (cell 0 b) => /(cell b a)
  /- 1 -/
  | cell _ (cell 1 b) => b
  /- 2 -/
  | cell a (cell 2 (cell b c)) =>
    (tar (cell a b)).bind fun ab =>
      (tar (cell a c)).bind fun ac =>
        tar (cell ab ac)
  /- 3 -/
  | cell a (cell 3 b) => (tar (cell a b)).map fun c =>
    ?(c)
  /- 4 -/
  | cell a (cell 4 b) => (tar (cell a b)).map fun c =>
    +(c)
  /- 5 -/
  | cell a (cell 5 (cell b c)) =>
    (tar (cell a b)).bind fun ab =>
      (tar (cell a c)).bind fun ac =>
        =(cell ab ac)

  /- sugar -/
  /- 6 -/
  | cell a (cell 6 (cell b (cell c d))) =>
    (tar (cell a (cell 4 (cell 4 b)))).bind fun a44b =>
      (tar (cell (cell 2 3) (cell 0 a44b))).bind fun a44b230 =>
        (tar (cell (cell c d) (cell 0 a44b230))).bind fun b =>
          tar (cell a b)
  /- 7 -/
  | cell a (cell 7 (cell b c)) =>
    (tar (cell a b)).bind fun ab =>
      tar (cell ab c)
  /- 8 -/
  | cell a (cell 8 (cell b c)) =>
    (tar (cell a b)).bind fun ab =>
      tar (cell ab c)
  /- 9 -/
  | cell a (cell 9 (cell b c)) =>
    (tar (cell a c)).bind fun ac =>
      tar (cell ac (cell 2 (cell (cell 0 1) (cell 0 b))))
  /- 10 -/
  | cell a (cell 10 (cell (cell b c) d)) =>
    (tar (cell a c)).bind fun ac =>
      (tar (cell a d)).bind fun ad =>
        #(cell b (cell ac ad))
  /- 11: hint -/
  | cell a (cell 11 (cell (cell _ c) d)) =>
    (tar (cell a c)).bind fun ac =>
      (tar (cell a d)).bind fun ad =>
        tar (cell (cell ac ad) (cell 0 3))
  | cell a (cell 11 (cell _ c)) => tar (cell a c)
  | _ => none
scoped prefix:50 "*" => tar

open DSL in #eval (*⟦⟦132 19⟧ ⟦11 37 ⟦4 0 3⟧⟧⟧) == some 20

def eval : Noun -> Option Noun
  | _ => none

end Interpreter
