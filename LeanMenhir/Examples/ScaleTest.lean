/-
**Regression test for the dependent-dispatcher scaling wall.**

A grammar with *more than ~15 productions* (here 21) exercises two things that
small examples (`CalcTemplate`, `StmCalc`) do not:

1. **Per-arm elaboration cost.** The dependent `actions` dispatcher reduces
   `prodLhsOf tables i` / `prodRhsRevOf tables i` once per arm. Backed by plain
   `Array.getD` these reductions are `O(i)` (the kernel walks the backing `List`),
   giving `O(numProd²)` total work and large retained intermediate state — which
   made BNFC-sized grammars (e.g. L0, 256 productions) OOM. `build_tables%` now
   compiles those lookups into balanced decision trees (`prodLhsFn`/`prodRhsRevFn`),
   so each reduction is `O(log numProd)`.

2. **`Fin`-literal exhaustiveness.** Lean's equation compiler only proves a
   `Fin n` numeric-literal match exhaustive (using the `isLt` bound to rule out
   `val ≥ n`) for *small* `n`; past ~15 arms it reports the out-of-range index as
   a "missing case". The trailing `⟨_ + (numProd+1), h⟩ => elimOutOfRange h` arm
   discharges that impossible case so the match type-checks.

If either regresses, this file stops compiling. The grammar is

    Sel ::= "c0" | "c1" | … | "c19" ;     -- 20 keyword alternatives

with `Sel` carrying the selected index. Certified by **kernel `decide`** (so the
jump-table lookups are also exercised inside the validators).

LGPL-3.0-or-later (derivative of coq-menhirlib).
-/
import LeanMenhir.Runtime
import LeanMenhir.Generator.BuildTables

namespace LeanMenhir.Examples.ScaleTest

open LeanMenhir LeanMenhir.Gen

/-! Terminals: `c0..c19` = 0..19, EOF = 20  (numTerm = 21).
Nonterminals: Start = 0, Sel = 1  (numNonterm = 2). -/

def grammar : Grammar0 where
  numTerm := 21
  numNonterm := 2
  start := 0
  eof := 20
  prods := #[
    (0, #[.nonterm 1, .term 20]),
    (1, #[.term 0]),
    (1, #[.term 1]),
    (1, #[.term 2]),
    (1, #[.term 3]),
    (1, #[.term 4]),
    (1, #[.term 5]),
    (1, #[.term 6]),
    (1, #[.term 7]),
    (1, #[.term 8]),
    (1, #[.term 9]),
    (1, #[.term 10]),
    (1, #[.term 11]),
    (1, #[.term 12]),
    (1, #[.term 13]),
    (1, #[.term 14]),
    (1, #[.term 15]),
    (1, #[.term 16]),
    (1, #[.term 17]),
    (1, #[.term 18]),
    (1, #[.term 19])
  ]

/-- Tables generated at elaboration time (jump-table-backed lookups). -/
def tables : GenTables := build_tables% grammar

def ntType : Fin (tables.numNonterm + 1) → Type
  | 2 => Unit   -- dummy nonterminal
  | _ => Nat    -- Start, Sel both carry the selected index
def termType : Fin (tables.numTerm + 1) → Type
  | _ => Unit

/-- 21-arm dependent dispatcher + the `elimOutOfRange` exhaustiveness shim. -/
def actions : (p : Fin (tables.numProd + 1)) →
    arrowsRight (symTypeOf tables ntType termType (.NT (prodLhsOf tables p)))
                ((prodRhsRevOf tables p).map (symTypeOf tables ntType termType))
  | 0 => fun (_ : Unit) (n : Nat) => n
  | 1 => fun (_ : Unit) => (0 : Nat)
  | 2 => fun (_ : Unit) => (1 : Nat)
  | 3 => fun (_ : Unit) => (2 : Nat)
  | 4 => fun (_ : Unit) => (3 : Nat)
  | 5 => fun (_ : Unit) => (4 : Nat)
  | 6 => fun (_ : Unit) => (5 : Nat)
  | 7 => fun (_ : Unit) => (6 : Nat)
  | 8 => fun (_ : Unit) => (7 : Nat)
  | 9 => fun (_ : Unit) => (8 : Nat)
  | 10 => fun (_ : Unit) => (9 : Nat)
  | 11 => fun (_ : Unit) => (10 : Nat)
  | 12 => fun (_ : Unit) => (11 : Nat)
  | 13 => fun (_ : Unit) => (12 : Nat)
  | 14 => fun (_ : Unit) => (13 : Nat)
  | 15 => fun (_ : Unit) => (14 : Nat)
  | 16 => fun (_ : Unit) => (15 : Nat)
  | 17 => fun (_ : Unit) => (16 : Nat)
  | 18 => fun (_ : Unit) => (17 : Nat)
  | 19 => fun (_ : Unit) => (18 : Nat)
  | 20 => fun (_ : Unit) => (19 : Nat)
  | 21 => ()
  | ⟨_ + 22, h⟩ => elimOutOfRange h

/-- The verified automaton built from the generated tables. -/
instance automaton : Automaton := automatonOfTablesTyped tables ntType termType Unit actions

/-- Safety — kernel `decide` (also exercises the jump-table lookups in the
validator, with no compiler-trust axiom). -/
theorem scaleSafe : Main.safeValidator (A := automaton) () = true := by decide

/-- Completeness — kernel `decide`. -/
theorem scaleComplete : Main.completeValidator (A := automaton) () = true := by decide

/-- The jump-table fields agree with the array fields they replace (catches reify
bugs in `build_tables%`). -/
example : (List.range tables.numProd).all
    (fun i => tables.prodLhsFn i == tables.prodLhs.getD i 0) = true := by native_decide
example : (List.range tables.numProd).all
    (fun i => tables.prodRhsRevFn i == tables.prodRhsRev.getD i #[]) = true := by native_decide

end LeanMenhir.Examples.ScaleTest
