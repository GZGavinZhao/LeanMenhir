/-
Port of `coq-menhirlib`'s `Alphabet.v` to Lean 4.

Original: Copyright Inria and CNRS, LGPL-3.0-or-later.
This Lean port is a derivative work, distributed under LGPL-3.0-or-later.

An "alphabet" is a type with a lawful, equality-deciding 3-way comparison and a
computable enumeration. This is the foundational typeclass on which the
grammar/automaton/parser are built.

Notes on the port:
* Coq's bespoke `Comparable`/`ComparableLeibnizEq` bundle is replaced by the
  core/Std vocabulary: `Ord α` supplies `compare`, `Std.TransOrd α` states that
  it is an oriented, transitive comparison, and `Std.LawfulEqOrd α` states that
  `compare x y = .eq` coincides with Leibniz equality. (Coq `comparison` ↦
  `Ordering`; Coq `CompOpp` ↦ `Ordering.swap`.)
* Coq `Finite.all_list` is kept as an *explicit, computable* `List α` (rather
  than Mathlib's `Fintype`, whose `Finset.toList` is noncomputable) so that the
  validators can be discharged by `decide` / `native_decide`.
-/
import Std

namespace LeanMenhir

/-! ### Decidable equality from a lawful comparison -/

/-- A lawful equality-deciding comparison yields `DecidableEq` (Coq
`comparable_decidable_eq` — there via `Comparable`+`ComparableLeibnizEq`, here
via core `Ord` + `Std.LawfulEqOrd`). Low priority so that hand-rolled instances
(e.g. `Fin.decEq`) win when available. -/
instance (priority := 100) instDecidableEqOfLawfulEqOrd
    {α : Type} [Ord α] [Std.LawfulEqOrd α] : DecidableEq α := fun x y =>
  if h : compare x y = .eq then
    .isTrue (Std.LawfulEqCmp.eq_of_compare h)
  else
    .isFalse (fun he => h (he ▸ Std.ReflCmp.compare_self))

/-! ### Finiteness and the `Alphabet` class -/

/-- A type with an explicit, computable list enumerating all its elements.
Mirrors Coq `Finite`. (Named `Enumerable` to avoid clashing with core's
`Finite`, and kept computable so validators reduce under `decide`.) -/
class Enumerable (α : Type) where
  allList : List α
  allList_complete : ∀ x : α, x ∈ allList

export Enumerable (allList allList_complete)

/-- **Decidable bounded quantification** over an enumerable type: the enabling
instance that lets universally-quantified `Prop`s over alphabets be discharged
by `decide` directly (no bespoke boolean combinators needed at statement
level). The decision procedure is a fold over `allList`. -/
instance Enumerable.decForall {α : Type} [Enumerable α] (p : α → Prop)
    [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (∀ x ∈ allList (α := α), p x)
    ⟨fun h x => h x (allList_complete x), fun h x _ => h x⟩

/-- An alphabet: an enumerable type whose `Ord.compare` is an oriented,
transitive comparison (`Std.TransOrd`) deciding Leibniz equality
(`Std.LawfulEqOrd`). Mirrors Coq `Alphabet`. -/
class Alphabet (α : Type) extends Ord α, Enumerable α where
  [transOrd : Std.TransOrd α]
  [lawfulEqOrd : Std.LawfulEqOrd α]

attribute [instance] Alphabet.transOrd Alphabet.lawfulEqOrd

end LeanMenhir
