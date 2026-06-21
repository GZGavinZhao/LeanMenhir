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
- **End-to-end demos — WORKING (two complementary paths):**
  - `Examples/Arith` — left-recursive `E → E + num | num`, tables straight from
    the in-Lean `Grammar0.buildTables` (`partial`, self-contained), safety by
    `native_decide`. Showcases the fully self-contained generator path.
  - `Examples/MiniCalc` — the real rocq-minicalc grammar (precedence, parens, a
    lexer, AST printer): 33-state automaton, tables emitted by `Gen.emitTables`
    as a concrete literal, safety certified by **kernel `decide`**
    (`minicalcSafe` axioms = `{propext, Quot.sound}` — *no* `Lean.ofReduceBool`/
    compiler-trust). Value tests (`1+2*3`, `(1+2)*3`, `1-2-3`, the Coq demo's
    `12 + 34*x / (48+y)` round-trip, and rejection of `1+`/`(1+2`) run the
    compiled parser via `native_decide`/`#eval`.

Key insights:
- `past_state` annotations are **one level longer** than `past_symb` (state-stack
  has one more element than the symbol-stack).
- Lean's definitional proof-irrelevance aligns the dependent eq-proofs
  (`Shift_act`/cast).
- **Kernel `decide` vs `native_decide`:** kernel `decide` gives a no-compiler-trust
  certificate but needs *concrete, non-`partial`* tables (so we emit them via
  `Gen.emitTables`) and a kernel-reducible validator — the one gotcha was
  `Array.contains` (doesn't kernel-reduce; switched the `past_state` predicate to
  `Array.toList.contains`). `native_decide` scales to large grammars but trusts
  the compiler. We offer both.

## M4 — Completeness (in progress)

Porting `Validator_complete.v` + `Interpreter_complete.v`.

**Done (builds clean, `sorry`-free):**
- `LeanMenhir/Validator/Complete.lean` — **complete.** The 8 invariants
  (`nullableStable`, `firstStable`, `startFuture`, `terminalShift`, `endReduce`,
  `nonTerminalGoto`, `startGoto`, `nonTerminalClosed`) bundled as `complete`; the
  boolean validator `isComplete`; and `complete_is_validator`. `stateHasFuture`
  is defined directly over `items_of_state` (membership) instead of Coq's
  AVL `FSet`/`FMap`; lookahead/first sets are plain `List`s. (The interpreter
  proof uses the 8 properties abstractly, so this is invisible there.)
- `LeanMenhir/Interpreter/Complete.lean` — **most of it:**
  - Part 1: `nullable_correct`/`first_correct` (fixpoint correctness),
    `first_word_set_app`, `ptlStackCompat` + `pop_stack_compat_pop_spec`.
  - Part 2: `PtZipper`/`PtlZipper`/`PtDot` (dotted parse trees), `ptdSem`,
    `ptdBuffer`, `ptlzProd`/`ptlzFuture`/`ptlzLookahead`,
    `ptz/ptlz/ptdStackCompat`, and helpers `ptlz_future_ptlz_prod`,
    `ptlz_future_first`, `ptz_stack_compat_cons_state_has_future`.
  - Part 3: `buildPtDotFromPt`/`_rec`/`_ptl`, `nextPtd`/`nextPtdIter`, and ALL
    four families of preservation lemmas: `sem_*`, `ptd_buffer_*`,
    `ptd_stack_compat_*` (incl. `stateHasFuture_of_ptzStackCompat`), and
    `ptd_cost_*` / `next_ptd_cost` / `next_ptd_iter_cost` (the 2^log_n_steps
    fuel bound).
  - `pop_eq_of_popSpec` (reverse of `pop_spec_ok`).

**Remaining (Part 4 + wiring):**
- `reduce_step_next_ptd`, `step_next_ptd`, `parse_fix_next_ptd_iter`,
  `parse_complete` — the step-correspondence lemmas relating the interpreter
  (`reduceStep`/`step`/`parseFix`/`parse`) to the `nextPtd` traversal.
- `Main.parse_complete` + `unambiguity`.

**Two specific Lean obstacles identified for Part 4** (both tractable, need care):
  1. *Evaluating `reduceStep`.* Its body has `let`-bound proof arguments
     (`hpref`) and a `match hpop : pop … with`; `rw [hpop]` fails ("motive not
     type correct" / proof-irrelevant `hpref` mismatch). `simp only [hpop]`
     rewrites value positions but not the `match`-discriminant. The working
     route is `unfold reduceStep; simp only [hpop]; split` (split the goto
     match) + `some`-injectivity + cast/`cast_heq` reconciliation, mirroring how
     `Interpreter/Correct.lean`'s `reduceStep_sound` splits.
  2. *Casing the zipper at a fixed nonterminal index.* `ptz : PtZipper init
     full_word (.NT (prod_lhs prod)) word` — `cases ptz` fails on the `Top_ptz`
     branch ("failed to solve `prod_lhs prod = start_nt init`"). Needs a
     generic-nonterminal helper (`ptz : PtZipper … (.NT nt) word`, `nt` a
     variable, `hnt : prod_lhs prod = nt`) where `cases ptz` works, with HEq/cast
     bridging at the `nt := prod_lhs prod` call site. (`nextPtdAux`,
     `sem_nextPtdAux`, `cost_nextPtdAux` already use this generic-`nt` pattern.)

## Remaining / future work
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
