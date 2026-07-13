/-
Port of `coq-menhirlib`'s `Alphabet.v` to Lean 4.

Original: Copyright Inria and CNRS, LGPL-3.0-or-later.
This Lean port is a derivative work, distributed under LGPL-3.0-or-later.

A "comparable" type is equipped with a 3-way `compare` defining a strict order;
an "alphabet" additionally has decidable (Leibniz) equality and is finite. These
are the foundational typeclasses on which the grammar/automaton/parser are built.

Notes on the port:
* Coq `comparison {Eq,Lt,Gt}` ↦ Lean `Ordering {eq,lt,gt}`; Coq `CompOpp` ↦
  `Ordering.swap`.
* Coq `Finite.all_list` is kept as an *explicit, computable* `List α` (rather than
  Mathlib's `Fintype`, whose `Finset.toList` is noncomputable) so that the
  validators can be discharged by `decide` / `native_decide`.
-/

namespace LeanMenhir

/-! ### Comparable types -/

/-- A comparable type is equipped with a `compare` function defining an order
relation. Mirrors Coq `Comparable`; `Ordering.swap` plays the role of `CompOpp`. -/
class Comparable (α : Type) where
  compare : α → α → Ordering
  compare_antisym : ∀ x y, (compare x y).swap = compare y x
  compare_trans : ∀ x y z c, compare x y = c → compare y z = c → compare x z = c

export Comparable (compare_antisym compare_trans)

@[simp] theorem compare_refl {α : Type} [Comparable α] (x : α) :
    Comparable.compare x x = Ordering.eq := by
  have h := compare_antisym x x
  cases hx : Comparable.compare x x <;> simp_all [Ordering.swap]

/-- Special case of comparable where equality is Leibniz equality. -/
class ComparableLeibnizEq (α : Type) [Comparable α] : Prop where
  compare_eq : ∀ x y : α, Comparable.compare x y = Ordering.eq → x = y

export ComparableLeibnizEq (compare_eq)

/-- Boolean equality derived from `compare`. -/
def compareEqb {α : Type} [Comparable α] (x y : α) : Bool :=
  match Comparable.compare x y with
  | Ordering.eq => true
  | _ => false

theorem compareEqb_iff {α : Type} [Comparable α] [ComparableLeibnizEq α] (x y : α) :
    compareEqb x y = true ↔ x = y := by
  unfold compareEqb
  constructor
  · intro h
    cases hc : Comparable.compare x y with
    | eq => exact compare_eq x y hc
    | lt => rw [hc] at h; simp at h
    | gt => rw [hc] at h; simp at h
  · rintro rfl; rw [compare_refl]

@[simp] theorem compareEqb_refl {α : Type} [Comparable α] [ComparableLeibnizEq α]
    (x : α) : compareEqb x x = true := by rw [compareEqb_iff]

/-- A comparable + Leibniz-eq type has decidable equality (reusing Mathlib's
`DecidableEq`). -/
instance (priority := 100) instDecidableEqOfComparable
    {α : Type} [Comparable α] [ComparableLeibnizEq α] : DecidableEq α := fun x y =>
  if h : Comparable.compare x y = Ordering.eq then
    .isTrue (compare_eq x y h)
  else
    .isFalse (fun he => h (he ▸ compare_refl x))

/-! ### Finiteness and the `Alphabet` class -/

/-- A type with an explicit, computable list enumerating all its elements.
Mirrors Coq `Finite`. (Named `Enumerable` to avoid clashing with Mathlib's
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

/-- An alphabet is a comparable type with Leibniz equality that is also finite.
Mirrors Coq `Alphabet`. -/
class Alphabet (α : Type) extends Comparable α, ComparableLeibnizEq α, Enumerable α

end LeanMenhir
