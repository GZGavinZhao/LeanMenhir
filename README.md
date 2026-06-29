# LeanMenhir

A formally verified LR(1) parser **interpreter + validator** for Lean 4, ported
from [`coq-menhirlib`](https://gitlab.inria.fr/fpottier/menhir) (the verified
parser library Menhir emits for Coq/CompCert), **plus a native LR(1) table
generator** that makes the package self-contained.

## Architecture (the key idea)

The LR table *generator* is **untrusted**. Separate **verified validators**
(`isSafe` for soundness, `isComplete` for completeness) check that generated
tables are consistent with the grammar, and a **verified interpreter** runs
validated tables. **Soundness, completeness, and unambiguity all hold whenever the
validators accept**, regardless of bugs in the generator — so you never have to
verify the (large, fiddly) LR table-construction algorithm.

* `LeanMenhir/Alphabet.lean` — `Comparable` / `ComparableLeibnizEq` /
  `Enumerable` / `Alphabet` typeclasses.
* `LeanMenhir/Grammar.lean` — symbols, the `Grammar` interface, and the
  dependently-typed `ParseTree` semantics.
* `LeanMenhir/Automaton.lean` — the LR automaton table interface, indexed by the
  grammar it parses (`Automaton (G : Grammar)`); the parser correctness theorems
  therefore read `[A : Automaton G]` and visibly concern `G`.
* `LeanMenhir/Validator/Safe.lean` — the safety validator `isSafe` with
  `safe_is_validator : isSafe = true → safe`, its converse, and
  `isSafe_iff_safe`/`instance : Decidable safe` (so a concrete automaton
  discharges `safe` with `by decide`/`by native_decide`).
* `LeanMenhir/Validator/Complete.lean` — the completeness validator `isComplete`
  and `complete_is_validator : isComplete = true → complete` (the eight LR(1)
  item-closure invariants). This validator is **sound-only** (the proposition
  `complete` is strictly weaker than `isComplete = true`, so — unlike `safe` —
  `complete` is not `Decidable`; discharge it via `complete_is_validator`).
* `LeanMenhir/Interpreter.lean` — `pop` / `reduceStep` / `step` / `parse`
  (fuel-based), with all stack-invariant lemmas. **No `sorry`.**
* `LeanMenhir/Interpreter/Correct.lean` — the soundness proof (`parse_correct`).
* `LeanMenhir/Interpreter/Complete.lean` — the completeness proof
  (`reduceStep`/`step`/`parseFix` follow the `next_ptd` traversal of the parse
  tree, giving `parse_complete`). **No `sorry`.**
* `LeanMenhir/Main.lean` — the user-facing entry points: the runnable `parse`,
  and the theorems `parse_correct` (soundness), `parse_complete` (completeness),
  and `unambiguity`. **No `sorry`** (axioms: `propext`, `Classical.choice`,
  `Quot.sound`).
* `LeanMenhir/Generator/` — the untrusted native LR generator (`LR1.lean`:
  `buildTables` = canonical LR(1), `buildTablesSLR` = SLR(1) with far fewer states;
  incl. `emitTables` for concrete output) and the `automatonOfTables` bridge that
  rebuilds a genuine `Automaton` from index data.
* `LeanMenhir/Examples/Arith.lean` — a generated parser for the **left-recursive**
  grammar `E → E + num | num` (which PEG/recursive-descent backends parse
  incorrectly); fully self-contained (in-Lean `buildTablesSLR`), with safety *and*
  completeness certificates by `native_decide`, and the instantiated
  `arith_correct` / `arith_parses` / `arith_unambiguous`.
* `LeanMenhir/Examples/MiniCalc.lean` — the real `rocq-minicalc` grammar
  (precedence, parens, lexer, AST printer); SLR(1) generated automaton (18 states,
  vs 33 for canonical LR(1)) whose
  safety *and* completeness certificates are discharged by **kernel `decide`**
  (axioms `{propext, Classical.choice, Quot.sound}` — crucially *no*
  compiler-trust axiom, i.e. no `Lean.ofReduceBool`), with the
  instantiated `mini_parses` / `mini_unambiguous`. Parses `12 + 34*x / (48+y)`
  to the expected AST, verified at build time.

## Trust / certificates

* **Soundness** (`Main.parse_correct`), **completeness** (`Main.parse_complete`),
  and **unambiguity** (`Main.unambiguity`) are kernel-checked, axioms
  `{propext, Classical.choice, Quot.sound}`. They hold for *any* automaton whose
  tables pass the validators — the untrusted generator is outside the trusted
  base.
* A grammar's **safety** and **completeness** certificates can each be obtained
  two ways: kernel `decide` on concrete emitted tables (no compiler trust; see
  MiniCalc), or `native_decide` on the in-Lean generator output (scales to large
  grammars; trusts the compiler — see Arith).

## Status

- Verified runtime + **soundness**, **completeness**, and **unambiguity**:
  complete, no `sorry` (axioms `{propext, Classical.choice, Quot.sound}`).
- Native LR(1) generator + two end-to-end examples (incl. completeness and
  unambiguity instantiated on both): working.

See `docs/progress.md` for details and `docs/lean-menhir-handoff.md` for the
original plan.

## License

LGPL-3.0-or-later (derivative of `coq-menhirlib`, © Inria/CNRS).
