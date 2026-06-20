/-
`Comparable` / `Enumerable` / `Alphabet` instances for `Fin n`, used as the
index types (terminals, nonterminals, productions, states) of *generated*
automata. Part of the (untrusted) generator support.

LGPL-3.0-or-later (derivative of coq-menhirlib).
-/
import LeanMenhir.Alphabet
import Mathlib.Data.List.FinRange

namespace LeanMenhir

/-- 3-way comparison on `Fin n` via the underlying naturals. -/
def Fin.cmp {n : Nat} (a b : Fin n) : Ordering :=
  if a.val < b.val then .lt else if a.val = b.val then .eq else .gt

instance instComparableFin {n : Nat} : Comparable (Fin n) where
  compare := Fin.cmp
  compare_antisym a b := by
    show (Fin.cmp a b).swap = Fin.cmp b a
    unfold Fin.cmp
    split_ifs <;> first | rfl | (exfalso; omega) | simp [Ordering.swap]
  compare_trans a b c o hab hbc := by
    simp only [Fin.cmp] at hab hbc ⊢
    split_ifs at hab hbc ⊢ <;>
      first
      | rfl
      | (exfalso; omega)
      | (rw [← hab] at hbc; exact absurd hbc (by decide))
      | simp_all

instance instComparableLeibnizEqFin {n : Nat} : ComparableLeibnizEq (Fin n) where
  compare_eq a b h := by
    apply Fin.ext
    simp only [show Comparable.compare a b = Fin.cmp a b from rfl, Fin.cmp] at h
    split_ifs at h <;> simp_all

instance instEnumerableFin {n : Nat} : Enumerable (Fin n) where
  allList := List.finRange n
  allList_complete x := List.mem_finRange x

instance instAlphabetFin {n : Nat} : Alphabet (Fin n) := {}

end LeanMenhir
