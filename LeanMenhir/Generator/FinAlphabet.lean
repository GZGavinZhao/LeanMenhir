/-
`Alphabet` instances for `Fin n`, used as the index types (terminals,
nonterminals, productions, states) of *generated* automata. Part of the
(untrusted) generator support.

The comparison is core's `Ord (Fin n)` (compare the underlying naturals);
its lawfulness (`Std.TransOrd`, `Std.LawfulEqOrd`) ships with Std, so only the
enumeration needs defining here.

LGPL-3.0-or-later (derivative of coq-menhirlib).
-/
import LeanMenhir.Spec.Alphabet

namespace LeanMenhir

instance instEnumerableFin {n : Nat} : Enumerable (Fin n) where
  allList := List.finRange n
  allList_complete x := List.mem_finRange x

instance instAlphabetFin {n : Nat} : Alphabet (Fin n) := {}

end LeanMenhir
