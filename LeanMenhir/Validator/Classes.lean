/-
Port of `coq-menhirlib`'s `Validator_classes.v` to Lean 4.

Original: Copyright Inria and CNRS, LGPL-3.0-or-later.
This Lean port is a derivative work, distributed under LGPL-3.0-or-later.

In Coq, `IsValidator` is a reflection typeclass whose instances let Coq's
`Derive` machinery *synthesize* the boolean validator from the `Prop`
specification. Lean has no comparable term-synthesis-from-typeclass mechanism,
so we instead define the boolean validators explicitly and prove the
`b = true → P` implications by hand. This file collects the reusable lemmas
(`forallb`-style combinators) used by both `Validator/Safe` and
`Validator/Complete`.
-/
import LeanMenhir.Alphabet

namespace LeanMenhir

/-- `b = true` entails `P`. Mirrors Coq `IsValidator`. -/
def IsValidator (P : Prop) (b : Bool) : Prop := b = true → P

theorem IsValidator.elim {P : Prop} {b : Bool} (h : IsValidator P b) : b = true → P := h

/-- Boolean "for all elements of the finite alphabet `α`" (Coq `forallb b all_list`). -/
def Allb (α : Type) [Enumerable α] (f : α → Bool) : Bool := (allList (α := α)).all f

/-- A boolean check over all elements of a finite alphabet validates a universal
statement (Coq `is_validator_forall_finite`). -/
theorem forall_of_Allb {α : Type} [Enumerable α] {f : α → Bool} {P : α → Prop}
    (hf : ∀ x, f x = true → P x) (h : Allb α f = true) : ∀ x, P x := by
  intro x
  rw [Allb, List.all_eq_true] at h
  exact hf x (h x (allList_complete x))

/-- Converse of `forall_of_Allb`: if the boolean check holds for every element,
the `Allb` is `true`. Used by the reverse ("validator completeness") direction
that powers the `Decidable safe`/`Decidable complete` instances. -/
theorem Allb_of_forall {α : Type} [Enumerable α] {f : α → Bool}
    (h : ∀ x, f x = true) : Allb α f = true := by
  rw [Allb, List.all_eq_true]
  exact fun x _ => h x

end LeanMenhir
