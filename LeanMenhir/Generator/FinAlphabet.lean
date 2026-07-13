/-
`Comparable` / `Enumerable` / `Alphabet` instances for `Fin n`, used as the
index types (terminals, nonterminals, productions, states) of *generated*
automata. Part of the (untrusted) generator support.

LGPL-3.0-or-later (derivative of coq-menhirlib).
-/
import LeanMenhir.Spec.Alphabet

namespace LeanMenhir

/-- 3-way comparison on `Fin n` via the underlying naturals. -/
def Fin.cmp {n : Nat} (a b : Fin n) : Ordering :=
  if a.val < b.val then .lt else if a.val = b.val then .eq else .gt

instance instComparableFin {n : Nat} : Comparable (Fin n) where
  compare := Fin.cmp
  compare_antisym a b := by
    show (Fin.cmp a b).swap = Fin.cmp b a
    unfold Fin.cmp; grind [Ordering.swap]
  compare_trans a b c o hab hbc := by
    simp only [Fin.cmp] at hab hbc ⊢; grind

instance instComparableLeibnizEqFin {n : Nat} : ComparableLeibnizEq (Fin n) where
  compare_eq a b h := by
    apply Fin.ext
    simp only [show Comparable.compare a b = Fin.cmp a b from rfl, Fin.cmp] at h
    grind

instance instEnumerableFin {n : Nat} : Enumerable (Fin n) where
  allList := List.finRange n
  allList_complete x := List.mem_finRange x

instance instAlphabetFin {n : Nat} : Alphabet (Fin n) := {}

end LeanMenhir
