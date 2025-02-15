section AST

abbrev Atom := Nat
inductive Noun
  | atom : Atom -> Noun
  | cell : Noun -> Noun -> Noun
deriving BEq, DecidableEq, Hashable

section Compat

instance : Coe Atom Noun := ⟨.atom⟩
instance : Coe Bool Noun where coe
  | true => .atom 0
  | false => .atom 1

instance : OfNat Noun n where ofNat := .atom n

class ToNoun (α : Type _) where
  toNoun : α -> Noun
export ToNoun (toNoun)

instance : ToNoun Atom where toNoun := Coe.coe
instance : ToNoun Bool where toNoun := Coe.coe
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
-- TODO: needs to handle nested lists
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

-- TODO: needs to handle nested lists
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
open Noun

declare_syntax_cat noun
scoped syntax num           : noun
scoped syntax "⟦" noun+ "⟧" : noun
scoped syntax noun          : term

instance : Coe (TSyntax `noun) (TSyntax `term) where coe n := ⟨n.raw⟩

macro_rules
  | `(noun| $num:num) => `(atom $num)
  | `(noun| ⟦$nouns:noun* $noun:noun⟧) => do
    let mut acc : TSyntax `term <- `($noun)
    for noun in nouns.reverse do acc <- `(cell $noun $acc)
    return acc
  | `(term| $noun:noun) => `(noun| $noun)

#guard ⟦1⟧ == atom 1
#guard ⟦1 2⟧ == cell 1 2
#guard ⟦⟦1 2⟧⟧ == cell 1 2
#guard ⟦1 2 3⟧ == cell 1 (cell 2 3)
#guard ⟦⟦1 2⟧ 3⟧ == cell (cell 1 2) 3
#guard ⟦⟦1 2⟧ 3 4⟧ == cell (cell 1 2) (cell 3 4)
#guard ⟦1 ⟦2 3⟧⟧ == cell 1 (cell 2 3)
#guard ⟦1 2 ⟦3 4⟧⟧ == cell 1 (cell 2 (cell 3 4))
#guard ⟦1 2 3 4⟧ == cell 1 (cell 2 (cell 3 4))
#guard ⟦⟦1 2⟧ ⟦3 4⟧⟧ == cell (cell 1 2) (cell 3 4)

end DSL

namespace Interpreter

open Noun

/- ?, cell or atom -/
def wut : Noun -> Noun
  | atom _ => 1
  | cell _ _ => 0
scoped prefix:50 "?" => wut

open DSL in #guard (?⟦1⟧) == ⟦1⟧
open DSL in #guard (?⟦1 2⟧) == ⟦0⟧

/- +, increment -/
def lus : Noun -> Noun
  | atom a => atom (a + 1)
  | cell a b => cell a b
scoped prefix:50 "+" => lus

open DSL in #guard (+⟦1⟧) == ⟦2⟧
open DSL in #guard (+⟦1 2⟧) == ⟦1 2⟧

/- =, equality -/
def tis : Noun -> Option Noun
  | cell a b => if a == b then atom 0 else atom 1
  | _ => none
scoped prefix:50 "=" => tis

open DSL in #guard (=⟦1⟧) == none
open DSL in #guard (=⟦1 2⟧) == ⟦1⟧
open DSL in #guard (=⟦2 2⟧) == ⟦0⟧
open DSL in #guard (=⟦⟦2 2⟧ ⟦2 3⟧⟧) == ⟦1⟧
open DSL in #guard (=⟦⟦2 3⟧ ⟦2 3⟧⟧) == ⟦0⟧

/- /, slot (tree addressing operator) -/
def fas : Noun -> Option Noun
  | cell 0 _ => none
  | cell 1 a => a
  | cell 2 (cell a _) => a
  | cell 3 (cell _ b) => b
  -- | cell (atom a) b =>
  -- using structural recursion? instead
  | cell (atom (Nat.succ a)) b =>
    match (fas (cell ↑((a + 1) / 2) b)) with
      | some (cell b c) => if (a + 1) % 2 == 0 then b else c
      | _ => none
  | _ => none
scoped prefix:50 "/" => fas

/-
     1
  2     3
4  5  6  7
       14 15
-/
open DSL in #guard (/⟦1 ⟦⟦4 5⟧ ⟦6 14 15⟧⟧⟧) == ⟦⟦4 5⟧ ⟦6 14 15⟧⟧
open DSL in #guard (/⟦2 ⟦⟦4 5⟧ ⟦6 14 15⟧⟧⟧) == ⟦4 5⟧
open DSL in #guard (/⟦3 ⟦⟦4 5⟧ ⟦6 14 15⟧⟧⟧) == ⟦6 14 15⟧
open DSL in #guard (/⟦4 ⟦⟦4 5⟧ ⟦6 14 15⟧⟧⟧) == ⟦4⟧
open DSL in #guard (/⟦5 ⟦⟦4 5⟧ ⟦6 14 15⟧⟧⟧) == ⟦5⟧
open DSL in #guard (/⟦6 ⟦⟦4 5⟧ ⟦6 14 15⟧⟧⟧) == ⟦6⟧
open DSL in #guard (/⟦7 ⟦⟦4 5⟧ ⟦6 14 15⟧⟧⟧) == ⟦14 15⟧
open DSL in #guard (/⟦8 ⟦⟦4 5⟧ ⟦6 14 15⟧⟧⟧) == none
--
open DSL in #guard (/⟦13 ⟦⟦4 5⟧ ⟦6 14 15⟧⟧⟧) == none
open DSL in #guard (/⟦14 ⟦⟦4 5⟧ ⟦6 14 15⟧⟧⟧) == ⟦14⟧

/- #, edit (replaces part of a noun with another) -/
partial def hax : Noun -> Option Noun
  | cell 1 (cell a _) => a
  -- | cell (atom (Nat.succ a)) (cell b c) => match (/(cell (atom (a)) c)) with
  --   | some d => if (a + 1) % 2 == 0
  --     then hax (cell (atom ((a + 1) / 2)) (cell (cell b d) c))
  --     else hax (cell (atom ((a) / 2)) (cell (cell d b) c))
  --   | _ => none
  | cell (atom (Nat.succ a)) (cell b c) => if (a + 1) % 2 == 0
    then (/(cell ↑(a + 2) c)).bind
      fun d => hax (cell ↑((a + 1) / 2) (cell (cell b d) c))
    else (/(cell a c)).bind
      fun d => hax (cell ↑((a) / 2) (cell (cell d b) c))
  | _ => none
scoped prefix:50 "#" => hax

/-
  22  33

-/
open DSL in #guard (#⟦2 11 ⟦22 33⟧⟧) == ⟦11 33⟧
open DSL in #guard (#⟦3 11 ⟦22 11⟧⟧) == ⟦22 11⟧

open DSL in #guard (#⟦2 11 ⟦⟦22 33⟧ 44⟧⟧) == ⟦11 44⟧
open DSL in #guard (#⟦3 11 ⟦⟦22 33⟧ 44⟧⟧) == ⟦⟦22 33⟧ 11⟧
open DSL in #guard (#⟦4 11 ⟦⟦22 33⟧ 44⟧⟧) == ⟦⟦11 33⟧ 44⟧
open DSL in #guard (#⟦5 11 ⟦⟦22 33⟧ 44⟧⟧) == ⟦⟦22 11⟧ 44⟧

/-
  22  33
     44 55
-/
open DSL in #guard (#⟦1 ⟦123 456⟧ ⟦22 33 44 55⟧⟧) == ⟦123 456⟧
open DSL in #guard (#⟦2 ⟦123 456⟧ ⟦22 33 44 55⟧⟧) == ⟦⟦123 456⟧ 33 44 55⟧
open DSL in #guard (#⟦3 ⟦123 456⟧ ⟦22 33 44 55⟧⟧) == ⟦22 123 456⟧
open DSL in #guard (#⟦4 ⟦123 456⟧ ⟦22 33 44 55⟧⟧) == none
open DSL in #guard (#⟦5 ⟦123 456⟧ ⟦22 33 44 55⟧⟧) == none
open DSL in #guard (#⟦6 ⟦123 456⟧ ⟦22 33 44 55⟧⟧) == ⟦22 ⟦⟦123 456⟧ ⟦44 55⟧⟧⟧
open DSL in #guard (#⟦7 ⟦123 456⟧ ⟦22 33 44 55⟧⟧) == ⟦22 33 ⟦123 456⟧⟧
open DSL in #guard (#⟦8 ⟦123 456⟧ ⟦22 33 44 55⟧⟧) == none
--
open DSL in #guard (#⟦13 ⟦123 456⟧ ⟦22 33 44 55⟧⟧) == none
open DSL in #guard (#⟦14 ⟦123 456⟧ ⟦22 33 44 55⟧⟧) == ⟦22 ⟦33 ⟦⟦123 456⟧ 55⟧⟧⟧
open DSL in #guard (#⟦15 ⟦123 456⟧ ⟦22 33 44 55⟧⟧) == ⟦22 ⟦33 ⟦44 ⟦123 456⟧⟧⟧⟧

/- *, eval -/
partial def tar : Noun -> Option Noun
  /- core -/
  /-
  0: address at slot
  locates a noun at address b in subject a
  -/
  | cell a (cell 0 b) => /(cell b a)
  /-
  1: constant
  return the formula
  -/
  | cell _ (cell 1 b) => b
  /-
  2: evaluate
  modify the subject against which a second formula is evaluated
  can be thought of as "a way of storing a subprocedure in a subject, then
  accessing it for evaluation"
  fs = f(s); gs = g(s); gs(fs)
  -/
  | cell s (cell 2 (cell f g)) =>
    (tar (cell s f)).bind fun fs =>
      (tar (cell s g)).bind fun gs =>
        tar (cell fs gs)
  /-
  3: distinguish cell or atom
  does f applied to s resolve to a cell?
  -/
  | cell s (cell 3 f) => (tar (cell s f)).map wut
  /-
  4: increment
  [eval, then] increment the subject
  -/
  | cell s (cell 4 f) => (tar (cell s f)).map lus
  /-
  5: test for equality
  are the two nouns, as resolved against the subject, identical?
  -/
  | cell s (cell 5 (cell f g)) =>
    (tar (cell s f)).bind fun fs =>
      (tar (cell s g)).bind fun gs =>
        =(cell fs gs)
  /-
  distribution
  formula is a cell == each contained noun is a formula
  fgs = fg(s); hs = h(s); (fgs hs)
  -/
  | cell s (cell (cell f g) h) =>
    (tar (cell s (cell f g))).bind fun fgs =>
      (tar (cell s h)).bind fun hs =>
        cell fgs hs

  /- sugar -/
  /-
  6: conditional branch
  eval f(s), then increment twice to get (2,3) slot addr
  choose (2,3) slot based on condition
  choose (g,h) based on slot
  eval g(s) | h(s)
  -/
  | cell s (cell 6 (cell f (cell g h))) =>
    (tar (cell s (cell 4 (cell 4 f)))).bind fun cond =>
      (tar (cell (cell 2 3) (cell 0 cond))).bind fun slot =>
        (tar (cell (cell g h) (cell 0 slot))).bind fun g_or_h =>
          tar (cell s g_or_h)
  /-
  7: compose
  evaluation of one formula against the subject,
  then another formula against that result
  g ∘ f s
  -/
  | cell s (cell 7 (cell f g)) =>
    (tar (cell s f)).bind fun fs =>
      tar (cell fs g)
  /-
  8: extend
  pin a value into the subject
  -/
  | cell s (cell 8 (cell f g)) =>
    (tar (cell s f)).bind fun fs =>
      tar (cell fs g)
  /-
  9: invoke
  invoke a closure or compute over an association of code and data
  eval g against s, then eval the resulting formula in /⟦a s⟧
  -/
  | cell s (cell 9 (cell a f)) =>
    (tar (cell s f)).bind fun fs =>
      tar (cell fs (cell 2 (cell (cell 0 1) (cell 0 a))))
  /-
  10: replace at address
  -/
  | cell s (cell 10 (cell (cell f g) h)) =>
    (tar (cell s g)).bind fun gs =>
      (tar (cell s h)).bind fun hs =>
        #(cell f (cell gs hs))
  /-
  11: hint
  provide an arbitrary annotation for a computation w/o changing the result
  in practice, signals to the runtime to do something Nock doesn't know about
  -/
  | cell s (cell 11 (cell (cell _f g) h)) =>
    (tar (cell s g)).bind fun gs =>
      (tar (cell s h)).bind fun hs =>
        tar (cell (cell gs hs) (cell 0 3))
  | cell s (cell 11 (cell _f g)) => tar (cell s g)
  | _ => none
scoped prefix:50 "*" => tar

/- nock 0 -/
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦3 4⟧⟧ ⟦0 2⟧⟧) == ⟦1 2⟧
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦3 4⟧⟧ ⟦0 4⟧⟧) == ⟦1⟧
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦3 4⟧⟧ ⟦0 8⟧⟧) == none
/- nock 1 -/
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦3 4⟧⟧ ⟦1 7⟧⟧) == ⟦7⟧
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦3 4⟧⟧ ⟦1 ⟦7 8 9⟧⟧⟧) == ⟦7 8 9⟧
/- nock 2 -/
open DSL in #guard (*⟦⟦1 2⟧ ⟦2 ⟦0 2⟧ ⟦1 ⟦0 1⟧⟧⟧⟧) == ⟦1⟧
/- nock 3 -/
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦3 4⟧⟧ ⟦3 0 1⟧⟧) == ⟦0⟧
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦3 4⟧⟧ ⟦3 0 4⟧⟧) == ⟦1⟧
/- nock 4 -/
open DSL in #guard (*⟦5 ⟦4 0 1⟧⟧) == ⟦6⟧
/- nock 5 -/
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦1 2⟧⟧ ⟦5 ⟦0 2⟧ ⟦0 3⟧⟧⟧) == ⟦0⟧
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦3 4⟧⟧ ⟦5 ⟦0 2⟧ ⟦0 3⟧⟧⟧) == ⟦1⟧
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦1 2⟧⟧ ⟦5 ⟦0 5⟧ ⟦4 0 4⟧⟧⟧) == ⟦0⟧
/-
distribution
s ⟦0 3⟧ == ⟦3 4⟧
s [4 0 5] == +/⟦5 s⟧ == 3
-/
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦3 4⟧⟧ ⟦⟦0 3⟧ ⟦4 0 5⟧⟧⟧) == ⟦⟦3 4⟧ 3⟧
/- nock 6 -/
/- nock 7 -/
/- nock 8 -/
/- nock 9 -/
/- nock 10 -/
/- nock 11 -/
open DSL in #guard (*⟦⟦132 19⟧ ⟦11 37 ⟦4 0 3⟧⟧⟧) == ⟦20⟧

def nock : Noun -> Option Noun
  | _ => none

end Interpreter
