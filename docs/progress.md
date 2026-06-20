# LeanMenhir Porting Progress

Tracking the port of `coq-menhirlib` (`refs/menhir/coq-menhirlib/src/*.v`) to
Lean 4. See `lean-menhir-handoff.md` for the overall plan and milestones.

## Design decisions (recorded per handoff §9)

- **Mathlib dependency: YES.** Already wired in `lakefile.toml` (`v4.31.0`, matches
  `lean-toolchain`). We reuse Mathlib for `Fintype`, `DecidableEq`, `List`/`Nat`
  lemmas, `Ordering`, and tactics (`omega`, `simp`, `rcases`, ...).
- **Alphabet encoding:** custom `Comparable` / `ComparableLeibnizEq` classes
  mirroring Coq (3-way `compare : α → α → Ordering`, `Ordering.swap` plays the
  role of Coq `CompOpp`). The `Alphabet` class bundles `Comparable` +
  `ComparableLeibnizEq` + Mathlib `Fintype` (so `all_list := Finset.univ.toList`,
  reusing Mathlib finiteness). Custom `compare` kept because (a) the validators
  are defined in terms of `compare_eqb` / `all_list` exactly as in Coq, and (b)
  the completeness milestone (M4) needs an ordered map keyed by `compare`.
- **Module functor encoding:** Coq `Module Type`s become Lean **classes**
  (`Grammar`, `Automaton extends Grammar`), bundling all parameters as fields.
  Code is written in `section`s with `variable [Automaton]` etc. One
  grammar/automaton is "in scope" at a time, which matches how generated parsers
  are used. Alphabet sub-instances are re-exposed as global projection-instances.
- **Termination:** fuel (`log_n_steps`, budget `2^n`) exactly as Coq. No
  well-founded recursion.
- **Scope for v1:** soundness (M3) is the priority MVP; completeness (M4) is a
  stretch goal pursued after M3 + M5.

## Milestone status

- [x] M0 — Skeleton + `Alphabet.lean`
- [~] M1 — `Grammar.lean` done (Symbol + Alphabet instances, `Grammar` class,
  `ParseTree`/`ParseTreeList`, `ptSem`/`ptlSem`, `ptSize`/`ptlSize`). A trivial
  grammar instance typechecks and `ptSize`/`ptSem` evaluate. `Automaton.lean` next.

## Current state (summary)

- **Verified runtime — DONE, no `sorry`:** `Alphabet`, `Grammar`, `Automaton`,
  `Validator/Classes`, `Validator/Safe` (incl. `safe_is_validator`),
  `Interpreter` (`pop`, `reduceStep`, `step`, `parseFix`, `parse` + all stack-
  invariant lemmas).
- **Soundness — DONE, no `sorry`:** `pop_spec_ptl`, `reduceStep_sound`,
  `step_sound`, `parseFix_sound`, and the user-facing `Main.parse_correct` are all
  proved. `#print axioms Main.parse_correct` = `{propext, Classical.choice,
  Quot.sound}` (no `sorryAx`).
- **Native LR(1) generator (untrusted, `partial def`) — WORKING:**
  `Generator/FinAlphabet` (Fin alphabets), `Generator/Tables`
  (`GenTables` + `automatonOfTables`: rebuilds the dependent `Automaton` from
  index data, reconstructing `Shift_act`/`goto` proofs via `DecidableEq`),
  `Generator/LR1` (canonical LR(1): nullable/first, closure/goto, state
  collection, action/goto tables, stack-shape fixpoints for `past_symb`/
  `past_state`).
- **End-to-end demo — WORKING:** `Examples/Arith` generates a parser for the
  left-recursive `E → E + num | num` grammar; `isSafe` is discharged by
  `native_decide`, and `parse` of `1 + 2 + 3` gives `6` (the case PEG/recursive-
  descent backends get wrong). Bad input is rejected. All checked by
  `native_decide` at build time, and `Main.parse_correct` specialises to it.

Key insights: `past_state` annotations are **one level longer** than `past_symb`
(the state-stack has one more element than the symbol-stack); Lean's definitional
proof-irrelevance lets the dependent eq-proofs (`Shift_act`/cast) be aligned.

## Remaining / future work

- M4: completeness validator (`Validator_complete.v`) + `Interpreter_complete.v`
  (`parse_complete`, `unambiguity`). Needs `items_of_state` + ordered terminal
  sets/maps. The generator already records LR(1) items per state internally.
- Cosmetic: `automatonOfTables` reducible-instance warning.
- BNFC `--lean` backend integration to emit `Grammar0` from `.cf` files.
- [ ] M2 — `Interpreter.lean` (executable)
- [ ] M3 — Soundness (`Validator/Classes`, `Validator/Safe`, `Interpreter/Correct`, `Main.parse_correct`)
- [ ] M4 — Completeness + unambiguity
- [ ] M5 — MiniCalc end-to-end example

## Notes / gotchas

- `CompOpp` ↦ `Ordering.swap`; `comparison {Eq,Lt,Gt}` ↦ `Ordering {eq,lt,gt}`.
- Coq `Finite.all_list` ↦ explicit computable `Enumerable.allList`.
- **No `thunkP`/`reprove`/`cast` machinery needed.** Coq used it so `vm_compute`
  wouldn't reduce proof terms; Lean erases `Prop` at compile time, so the
  interpreter carries equality proofs directly and uses `cast`/`▸`. Casts are
  no-ops at runtime, so `#eval parse` still works; the validators are pure `Bool`
  (no casts) so `decide`/`native_decide` work too.
- Validators are defined explicitly as `Bool` (not synthesized from the
  `IsValidator` typeclass as in Coq), with hand proofs `isX = true → X`.
