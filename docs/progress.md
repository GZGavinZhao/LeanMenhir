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
  `ComparableLeibnizEq` + a custom computable `Enumerable` (an explicit `allList`
  with a completeness proof, mirroring Coq's `Finite.all_list` — *not* Mathlib
  `Fintype`, which is used only by the untrusted `Generator/`). Custom `compare`
  kept because the validators are defined in terms of `compare_eqb` / `allList`
  exactly as in Coq.
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
- **Native LR generator (untrusted, `partial def`) — WORKING:**
  `Generator/FinAlphabet` (Fin alphabets), `Generator/Tables`
  (`GenTables` + `automatonOfTables`: rebuilds the dependent `Automaton` from
  index data, reconstructing `Shift_act`/`goto` proofs via `DecidableEq`),
  `Generator/LR1`: `buildTables` (canonical LR(1)) and `buildTablesSLR`
  (**SLR(1)** — LR(0) states + `FOLLOW`-set reduce lookaheads, so far fewer states
  than canonical LR(1): MiniCalc 33→18). Both share nullable/first, closure/goto,
  state collection, action/goto tables, and the `past_symb`/`past_state`
  stack-shape fixpoints. SLR items carry `FOLLOW(lhs)` (start items the full
  alphabet), which satisfies the completeness validator for conflict-free SLR
  grammars; if SLR introduces a conflict the `isComplete` certificate simply fails
  (soundness still holds). Both example grammars validate `isSafe` *and*
  `isComplete` under SLR.
- **End-to-end demos — WORKING (two complementary paths):**
  - `Examples/Arith` — left-recursive `E → E + num | num`, tables straight from
    the in-Lean `Grammar0.buildTablesSLR` (`partial`, self-contained), safety by
    `native_decide`. Showcases the fully self-contained generator path.
  - `Examples/MiniCalc` — the real rocq-minicalc grammar (precedence, parens, a
    lexer, AST printer): SLR(1) automaton (18 states, vs 33 for canonical LR(1)),
    tables emitted by `Gen.emitTables`
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

## M4 — Completeness (DONE, `sorry`-free)

Full port of `Validator_complete.v` + `Interpreter_complete.v` + the `Main.v`
completeness/unambiguity theorems. `#print axioms Main.parse_complete` =
`#print axioms Main.unambiguity` = `{propext, Classical.choice, Quot.sound}` (no
`sorryAx`, no `Lean.ofReduceBool` — soundness *and* completeness are kernel-proven;
only the per-grammar safety/completeness certificates use `decide`/`native_decide`).

- `LeanMenhir/Validator/Complete.lean` — the 8 invariants (`nullableStable`,
  `firstStable`, `startFuture`, `terminalShift`, `endReduce`, `nonTerminalGoto`,
  `startGoto`, `nonTerminalClosed`) bundled as `complete`; the boolean validator
  `isComplete`; `complete_is_validator`. `stateHasFuture` is defined directly over
  `items_of_state` (membership) instead of Coq's AVL `FSet`/`FMap`;
  lookahead/first sets are plain `List`s. (The interpreter proof uses the 8
  properties abstractly, so this representation is invisible there.)
- `LeanMenhir/Interpreter/Complete.lean`:
  - Part 1: `nullable_correct`/`first_correct` (fixpoint correctness),
    `first_word_set_app`, `ptlStackCompat` + `pop_stack_compat_pop_spec`.
  - Part 2: `PtZipper`/`PtlZipper`/`PtDot` (dotted parse trees), `ptdSem`,
    `ptdBuffer`, `ptlzProd`/`ptlzFuture`/`ptlzLookahead`,
    `ptz/ptlz/ptdStackCompat`, helpers `ptlz_future_ptlz_prod`,
    `ptlz_future_first`, `ptz_stack_compat_cons_state_has_future`.
  - Part 3: `buildPtDotFromPt`/`_rec`/`_ptl`, `nextPtd`/`nextPtdIter`, and ALL
    four families of preservation lemmas: `sem_*`, `ptd_buffer_*`,
    `ptd_stack_compat_*` (incl. `stateHasFuture_of_ptzStackCompat`), and
    `ptd_cost_*` / `next_ptd_cost` / `next_ptd_iter_cost` (the 2^log_n_steps
    fuel bound). Plus `pop_eq_of_popSpec` (reverse of `pop_spec_ok`).
  - Part 4: the interpreter↔`next_ptd` correspondence —
    `reduceStep_progress_eq`/`reduceStep_accept_eq` (evaluate `reduceStep`),
    `reduceStep_next_ptdAux`/`reduceStep_next_ptd`, the three `step` evaluation
    lemmas (`step_eq_reduceStep_default`/`_lookahead`, `step_shift_eq`),
    `step_next_ptd`, `parseFix_next_ptd_iter`, and the top-level `parse_complete`.
- `LeanMenhir/Main.lean` — `completeValidator`, `parse_complete`, `unambiguity`.

How the two Part-4 obstacles were solved:
  1. *Evaluating `reduceStep`* (its body has `let`-bound proof args + a
     `match hpop : pop … with`). The working route is `unfold reduceStep;
     simp only [hpop]; split` on the goto match, then `injection` on the goto
     `some`-equation (proof irrelevance discards the `Prop`-valued `Sigma` second
     component), closing by `rfl`. Packaged as `reduceStep_progress_eq` /
     `reduceStep_accept_eq` so the main lemmas never fight the `let`s again.
  2. *Casing the zipper at a fixed nonterminal index.* The generic-`nt` helper
     `reduceStep_next_ptdAux` (`ptz : PtZipper … (.NT nt) word`, `nt` a variable,
     `hnt : prod_lhs prod = nt`, plus an explicit `pt` with
     `hpt : pt = hnt ▸ Non_terminal_pt prod ptl`) lets `cases ptz` succeed;
     `subst hnt; subst hpt` then cleans the rfl-cast, and `ptSem_recNT` bridges
     the residual semantic cast. `reduceStep_next_ptd` instantiates it at
     `nt := prod_lhs prod`, `hnt := rfl` (casts vanish).
  Other gotchas: reduce a `def`'s `match fut with` hypothesis with `dsimp only`
  (literal-cons) and the action-table `match` with `simp only [haction]`;
  `parseFix_next_ptd_iter` must `simp only [nextPtdIter, hni]` *before*
  `rw [parseFix_succ, hpf]` (simp chokes on `parseFix.match_1`'s
  overlapping-pattern equation lemmas if the match is already present), then
  `cases sr` mirrors `parseFix_sound`. `step_shift_eq` is stated over an explicit
  `Stream'.cons tok rest` (not `buffer.head`/`buffer.tail`) so the head reduces
  definitionally inside the proof.

## End-to-end completeness on the example grammars (DONE)

The generator now also emits the per-state LR(1) **item sets** (a new `GenTables.items`
field; `automatonOfTables.items_of_state` reads them), so the completeness
validator can run on generated automata. Two subtleties were needed:

- **Start items carry every terminal.** coq-menhirlib's `start_future` requires the
  initial state to predict each start production with *every* terminal as
  lookahead (not just `eof`). The generator seeds the initial item set with
  `⟨p, 0, t⟩` for all start productions `p` and all `t ∈ [0 : numTerm+1]` (the `+1`
  covers the padded `Fin (numTerm+1)` dummy terminal that `Allb`/`start_future`
  quantify over). These extra lookaheads only propagate along the non-nullable,
  eof-terminated start spine, so the rest of the canonical LR(1) automaton (state
  count, transitions, action/goto/past_* tables) is byte-for-byte unchanged.
- **The padded dummy production/nonterminal.** `Production`/`Nonterminal` are
  `Fin (n+1)` with a never-referenced dummy slot. The dummy production (empty RHS,
  clamped lhs) would spuriously trip `nullable_stable` and `start_future`, so
  `automatonOfTables` maps the dummy production's lhs to the dummy nonterminal and
  declares that nonterminal nullable — it never appears after a dot, so no real
  validator obligation touches it.

Results (`Examples/Arith.lean`, `Examples/MiniCalc.lean`):
- `isComplete_ok` / `minicalcComplete : completeValidator () = true` — Arith by
  `native_decide`, **MiniCalc by kernel `decide`** (`minicalcComplete` axioms =
  `{propext, Quot.sound}`, no compiler trust, just like its safety certificate).
- `arith_parses` / `mini_parses`: every parse tree with `ptSize tree ≤ 2^logNSteps`
  is parsed to its own value, consuming exactly the word (a clean corollary of
  `Main.parse_complete`).
- `arith_unambiguous` / `mini_unambiguous`: any two parse trees of a word have
  equal semantics (`Main.unambiguity`).

  (Stating the corollary without a `match` in its conclusion avoids a matcher
  mismatch: `Main.parse_complete`'s type uses an internal matcher
  `Main.parse_complete.match_1`, and a hand-written `match … with` over the stuck
  `Main.parse …` elaborates to a *different*, non-defeq matcher.)

## Remaining / future work
- Cosmetic: `automatonOfTables` reducible-instance warning.
- BNFC `--lean` backend integration to emit `Grammar0` from `.cf` files.
- [x] M2 — `Interpreter.lean` (executable)
- [x] M3 — Soundness (`Validator/Classes`, `Validator/Safe`, `Interpreter/Correct`, `Main.parse_correct`)
- [x] M4 — Completeness + unambiguity
- [x] M5 — MiniCalc end-to-end example

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
