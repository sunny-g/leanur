namespace Leanur.Nock

section AST

/-- a natural number, implemented as a `Nat` -/
abbrev Atom := Nat

/-- an `Atom` or a pair of `Noun`s -/
inductive Noun
  | atom : Atom → Noun
  | cell : Noun → Noun → Noun
deriving BEq, DecidableEq, Hashable, Inhabited

section Compat

class ToNoun (α : Type) where
  toNoun : α -> Noun

@[inline] instance : ToNoun Atom where toNoun := .atom
/- in nock, 0 == true, 1 == false -/
@[inline] instance : ToNoun Bool where toNoun : Bool -> Noun
  | true => .atom 0
  | false => .atom 1
@[inline] instance : ToNoun Noun := ⟨id⟩

@[inline] instance : OfNat Noun n where ofNat := .atom n

@[inline] instance : Coe Atom Noun := ⟨.atom⟩
@[inline] instance : Coe Bool Noun := ⟨ToNoun.toNoun⟩

open Std Format in
def Noun.toFormat : Noun → Format
  | .atom a => format a
  | .cell a b => format "⟦" ++ a.toFormat ++ " " ++ b.toFormat ++ "⟧"

def Noun.toString : Noun → String := ToString.toString ∘ Noun.toFormat

instance : Std.ToFormat Noun where format := Noun.toFormat
instance : ToString Noun where toString := Noun.toString

#guard Noun.toString (.atom 2) == "2"
#guard Noun.toString (.cell 1 2) == "⟦1 2⟧"
#guard Noun.toString (.cell 1 (.cell 2 3)) == "⟦1 ⟦2 3⟧⟧"
#guard Noun.toString (.cell (.cell 1 2) (.cell 3 4)) == "⟦⟦1 2⟧ ⟦3 4⟧⟧"

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
    let mut acc : TSyntax `term ← `($noun)
    for noun in nouns.reverse do acc ← `(cell $noun $acc)
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

/- ?, is cell (or atom) -/
def wut : Noun → Noun
  | atom _ => false
  | cell _ _ => true
scoped prefix:50 "?" => wut

open DSL in #guard (?⟦1 2⟧) == true
open DSL in #guard (?⟦1⟧) == false

/- +, increment -/
def lus : Noun → Noun
  | atom a => atom (a + 1)
  | cell a b => cell a b
scoped prefix:50 "+" => lus

open DSL in #guard (+⟦1⟧) == ⟦2⟧
open DSL in #guard (+⟦1 2⟧) == ⟦1 2⟧

/- =, equality -/
def tis : Noun → Option Noun
  | atom _ => none
  | cell a b => a == b
scoped prefix:50 "=" => tis

open DSL in #guard (=⟦1⟧) == none
open DSL in #guard (=⟦1 2⟧) == false
open DSL in #guard (=⟦2 2⟧) == true
open DSL in #guard (=⟦⟦2 2⟧ ⟦2 3⟧⟧) == false
open DSL in #guard (=⟦⟦2 3⟧ ⟦2 3⟧⟧) == true

/- /, slot (tree addressing operator) -/
def fas : Noun → Option Noun
  | cell 0 _ => none
  | cell 1 a => a
  | cell 2 (cell a _) => a
  | cell 3 (cell _ b) => b
  | cell (Nat.succ a) b => do
    match (← fas (cell ↑((a + 1) / 2) b)) with
      | cell b c => if (a + 1) % 2 == 0 then b else c
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
partial def hax : Noun → Option Noun
  | cell 1 (cell b _) => b
  -- | cell (atom (Nat.succ a)) (cell b c) => match (/(cell (atom (a)) c)) with
  --   | some d => if (a + 1) % 2 == 0
  --     then hax (cell (atom ((a + 1) / 2)) (cell (cell b d) c))
  --     else hax (cell (atom ((a) / 2)) (cell (cell d b) c))
  --   | _ => none
  | cell (Nat.succ a) (cell b c) => do
    if (a + 1) % 2 == 0
      then
        let d ← (/(cell ↑(a + 2) c))
        hax (cell ↑((a + 1) / 2) (cell (cell b d) c))
      else
        let d ← (/(cell a c))
        hax (cell ↑((a) / 2) (cell (cell d b) c))
  | _ => none
scoped prefix:50 "#" => hax

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
partial def tar : Noun → Option Noun
  /- core -/
  /-
  0: address at slot
  locates a noun at address b in subject a
  -/
  | cell a (cell 0 b) => /(cell b a)
  /-
  1: constant/quote
  return the noun
  -/
  | cell _a (cell 1 b) => b
  /-
  2: evaluate/apply
  modify the subject against which a second formula is evaluated
  can be thought of as "a way of storing a subprocedure in a subject, then
  accessing it for evaluation"
  fs = f(s); gs = g(s); gs(fs)
  -/
  | cell s (cell 2 (cell f g)) => do
    let fs ← tar (cell s f)
    let gs ← tar (cell s g)
    tar (cell fs gs)
  /-
  3: is cell
  does f applied to s resolve to a cell?
  -/
  | cell s (cell 3 f) => do ?(← tar (cell s f))
  /-
  4: increment
  [apply f to s] increment the result
  -/
  | cell s (cell 4 f) => do +(← tar (cell s f))
  /-
  5: equality
  are the two nouns, as resolved against the subject, identical?
  -/
  | cell s (cell 5 (cell f g)) => do
    let fs ← tar (cell s f)
    let gs ← tar (cell s g);
    =(cell fs gs)
  /-
  distribution/"implicit cons"/"cell-maker"
  when formula is a cell == each contained noun is a formula
  fgs = fg(s); hs = h(s); (fgs hs)
  -/
  | cell s (cell (cell f g) h) => do
    let fgs ← tar (cell s (cell f g))
    let hs ← tar (cell s h)
    cell fgs hs

  /- sugar -/
  /-
  6: if/then/else
  eval f(s), then increment twice to get (2,3) slot addr
  choose (2,3) slot based on condition
  choose (g,h) based on slot
  eval g(s) | h(s)
  -/
  | cell s (cell 6 (cell f (cell g h))) => do
    let cond ← tar (cell s (cell 4 (cell 4 f)))
    let slot ← tar (cell (cell 2 3) (cell 0 cond))
    let g_or_h ← tar (cell (cell g h) (cell 0 slot))
    tar (cell s g_or_h)
  /-
  7: compose/seq
  evaluation of one formula against the subject,
  then another formula against that result
  g ∘ f s
  -/
  | cell s (cell 7 (cell f g)) => do
    let fs ← tar (cell s f)
    tar (cell fs g)
  /-
  8: extend/push
  pin a value into the subject
  eval g against product of f and original subject s
  -/
  | cell s (cell 8 (cell f g)) => do
    let fs ← tar (cell s f)
    tar (cell (cell fs s) g)
  /-
  9: invoke/call
  invoke a closure or compute over an association of code and data
  eval f against s producing a core, then eval the contained formula against /⟦b s⟧
  -/
  | cell s (cell 9 (cell b f)) => do
    let fs ← tar (cell s f)
    tar (cell fs (cell 2 (cell (cell 0 1) (cell 0 b))))
  /-
  10: replace at address
  fs = f(s); gs = g(s); replace /⟦b gs⟧ with fs
  -/
  | cell s (cell 10 (cell (cell b f) g)) => do
    let fs ← tar (cell s f)
    let gs ← tar (cell s g)
    #(cell b (cell fs gs))
  /-
  11: hint
  provide an arbitrary annotation _f for a computation w/o changing the result
  in practice, signals to the runtime to do something Nock doesn't know about

  compute g against a, then throw away the result
  -/
  | cell s (cell 11 (cell (cell _f g) h)) => do
    let gs ← tar (cell s g)
    let hs ← tar (cell s h)
    tar (cell (cell gs hs) (cell 0 3))
  | cell s (cell 11 (cell _f g)) => tar (cell s g)
  | _ => none
scoped prefix:50 "*" => tar

/- nock 0 -/
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦3 6 7⟧⟧ ⟦0 1⟧⟧) == ⟦⟦1 2⟧ ⟦3 6 7⟧⟧
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦3 6 7⟧⟧ ⟦0 2⟧⟧) == ⟦⟦1 2⟧⟧
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦3 6 7⟧⟧ ⟦0 3⟧⟧) == ⟦⟦3 6 7⟧⟧
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦3 6 7⟧⟧ ⟦0 4⟧⟧) == ⟦1⟧
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦3 6 7⟧⟧ ⟦0 5⟧⟧) == ⟦2⟧
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦3 6 7⟧⟧ ⟦0 6⟧⟧) == ⟦3⟧
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦3 6 7⟧⟧ ⟦0 7⟧⟧) == ⟦6 7⟧
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦3 6 7⟧⟧ ⟦0 8⟧⟧) == none
/- nock 1 -/
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦3 4⟧⟧ ⟦1 7⟧⟧) == ⟦7⟧
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦3 4⟧⟧ ⟦1 ⟦7 8 9⟧⟧⟧) == ⟦7 8 9⟧
open DSL in #guard (*⟦42 ⟦1 153 218⟧⟧) == ⟦153 218⟧
open DSL in #guard (*⟦42 ⟦1 67⟧⟧) == ⟦67⟧
open DSL in #guard (*⟦42 ⟦1 ⟦2 587⟧⟧⟧) == ⟦2 587⟧
/- nock 2 -/
open DSL in #guard (*⟦⟦1 2⟧ ⟦2 ⟦0 2⟧ ⟦1 ⟦0 1⟧⟧⟧⟧) == ⟦1⟧
open DSL in #guard (*⟦77 ⟦2 ⟦1 42⟧ ⟦1 1 153 218⟧⟧⟧) == ⟦153 218⟧
/- nock 3 -/
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦3 4⟧⟧ ⟦3 0 1⟧⟧) == true
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦3 4⟧⟧ ⟦3 0 4⟧⟧) == false
open DSL in #guard (*⟦57 ⟦0 1⟧⟧) == ⟦57⟧
open DSL in #guard (*⟦57 ⟦4 0 1⟧⟧) == ⟦58⟧
/- nock 4 -/
open DSL in #guard (*⟦5 ⟦4 0 1⟧⟧) == ⟦6⟧
open DSL in #guard (*⟦5 ⟦4 4 0 1⟧⟧) == ⟦7⟧
open DSL in #guard (*⟦⟦132 19⟧ ⟦0 3⟧⟧) == ⟦19⟧
open DSL in #guard (*⟦⟦132 19⟧ ⟦4 0 3⟧⟧) == ⟦20⟧
open DSL in #guard (*⟦⟦132 19⟧ ⟦4 4 0 3⟧⟧) == ⟦21⟧
open DSL in #guard (*⟦⟦132 19⟧ ⟦4 4 4 0 3⟧⟧) == ⟦22⟧
/- nock 5 -/
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦1 2⟧⟧ ⟦5 ⟦0 2⟧ ⟦0 3⟧⟧⟧) == true
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦3 4⟧⟧ ⟦5 ⟦0 2⟧ ⟦0 3⟧⟧⟧) == false
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦3 5⟧⟧ ⟦5 ⟦0 5⟧ ⟦4 0 4⟧⟧⟧) == true
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦3 5⟧⟧ ⟦5 ⟦0 7⟧ ⟦4 4 0 6⟧⟧⟧) == true
/-
distribution
-/
open DSL in #guard (*⟦50 ⟦⟦0 1⟧ ⟦1 203⟧⟧⟧) == ⟦50 203⟧
open DSL in #guard (*⟦50 ⟦⟦0 1⟧ ⟦1 203⟧ ⟦0 1⟧ ⟦1 19⟧ ⟦1 76⟧⟧⟧) == ⟦50 203 50 19 76⟧
open DSL in #guard (*⟦⟦19 20⟧ ⟦0 1⟧ ⟦1 76⟧ ⟦4 4 0 3⟧⟧) == ⟦⟦19 20⟧ 76 22⟧
/-
s ⟦0 3⟧ == ⟦3 4⟧
s ⟦4 0 5] == +/⟦5 s⟧ == 3
-/
open DSL in #guard (*⟦⟦⟦1 2⟧ ⟦3 4⟧⟧ ⟦⟦0 3⟧ ⟦4 0 5⟧⟧⟧) == ⟦⟦3 4⟧ 3⟧
-- breaking it down
open DSL in #guard (*⟦42 ⟦4 0 1⟧⟧) == ⟦43⟧
open DSL in #guard (*⟦42 ⟦3 0 1⟧⟧) == ⟦1⟧
open DSL in #guard (*⟦42 ⟦⟦4 0 1⟧ ⟦3 0 1⟧⟧⟧) == ⟦43 1⟧

/- nock 6 -/
open DSL in #guard (*⟦42 ⟦6 ⟦1 0⟧ ⟦4 0 1⟧ ⟦1 233⟧⟧⟧) == ⟦43⟧
open DSL in #guard (*⟦42 ⟦6 ⟦1 1⟧ ⟦4 0 1⟧ ⟦1 233⟧⟧⟧) == ⟦233⟧
/- nock 7 -/
open DSL in #guard (*⟦42 ⟦7 ⟦4 0 1⟧ ⟦4 0 1⟧⟧⟧) == ⟦44⟧ -- increment twice
/- nock 8 -/
open DSL in #guard (*⟦42 ⟦8 ⟦4 0 1⟧ ⟦0 1⟧⟧⟧) == ⟦43 42⟧
open DSL in #guard (*⟦42 ⟦8 ⟦4 0 1⟧ ⟦4 0 3⟧⟧⟧) == ⟦43⟧
/- nock 9 -/
/- nock 10 -/
/- nock 11 -/
open DSL in #guard (*⟦⟦132 19⟧ ⟦11 37 ⟦4 0 3⟧⟧⟧) == ⟦20⟧

def nock : Noun → Option Noun
  | _ => none

end Interpreter

end Leanur.Nock
