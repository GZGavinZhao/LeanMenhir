# LeanMenhir

A formally verified LR(1) parser **interpreter + validator** for Lean 4, ported
from [`coq-menhirlib`](https://gitlab.inria.fr/fpottier/menhir) (the verified
parser library Menhir emits for Coq/CompCert), **plus a native LR(1) table
generator** that makes the package self-contained.

## Architecture (the key idea)

The LR table *generator* is **untrusted**. A separate **verified validator**
(`isSafe`) checks that generated tables are consistent with the grammar, and a
**verified interpreter** runs validated tables. **Soundness holds whenever the
validator accepts**, regardless of bugs in the generator — so you never have to
verify the (large, fiddly) LR table-construction algorithm.

* `LeanMenhir/Alphabet.lean` — `Comparable` / `ComparableLeibnizEq` /
  `Enumerable` / `Alphabet` typeclasses.
* `LeanMenhir/Grammar.lean` — symbols, the `Grammar` interface, and the
  dependently-typed `ParseTree` semantics.
* `LeanMenhir/Automaton.lean` — the LR automaton table interface.
* `LeanMenhir/Validator/Safe.lean` — the safety validator `isSafe` and
  `safe_is_validator : isSafe () = true → safe`.
* `LeanMenhir/Interpreter.lean` — `pop` / `reduceStep` / `step` / `parse`
  (fuel-based), with all stack-invariant lemmas. **No `sorry`.**
* `LeanMenhir/Interpreter/Correct.lean`, `LeanMenhir/Main.lean` — the soundness
  theorem `parse_correct`. **No `sorry`** (axioms: `propext`,
  `Classical.choice`, `Quot.sound`).
* `LeanMenhir/Generator/` — the untrusted native LR(1) generator
  (`LR1.lean`) and the `automatonOfTables` bridge that rebuilds a genuine
  `Automaton` from index data.
* `LeanMenhir/Examples/Arith.lean` — a generated parser for the **left-recursive**
  grammar `E → E + num | num` (which PEG/recursive-descent backends parse
  incorrectly); `parse [1,+,2,+,3] = 6`, verified at build time by `native_decide`.

## Status

- Verified runtime + **soundness**: complete, no `sorry`.
- Native LR(1) generator + end-to-end example: working.
- Completeness / unambiguity (`parse_complete`): future work.

See `docs/progress.md` for details and `docs/lean-menhir-handoff.md` for the
original plan.

## License

LGPL-3.0-or-later (derivative of `coq-menhirlib`, © Inria/CNRS).
