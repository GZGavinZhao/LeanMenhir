# LeanMenhir Porting Progress

Tracking the port of `coq-menhirlib` (`refs/menhir/coq-menhirlib/src/*.v`) to
Lean 4. See `lean-menhir-handoff.md` for the overall plan and milestones.

## 2026-06-25 — Scaling the typed dispatcher to BNFC-sized grammars

Driven by the BNFC backend's `LEANMENHIR-SCALING-HANDOFF.md`: the generated typed
`actions` dispatcher (one arm per production) did not scale to L0 (256 productions
/ 480 states) — it OOM'd / took minutes. Two independent walls were found and
fixed; the fix is internal (no break to the public bridge API).

1. **Per-arm `O(numProd²)` reduction → `O(numProd · log numProd)`.** The dependent
   return type of `actions` reduces `prodLhsOf tables i` / `prodRhsRevOf tables i`
   once per arm. Backed by `Array.getD` these are `O(i)` in the kernel reducer
   (it walks the backing `List`), and the retained intermediate state is what
   blew up memory. Added two jump-table fields to `GenTables` —
   `prodLhsFn : Nat → Nat` and `prodRhsRevFn : Nat → Array GSym` — that
   `build_tables%` populates with **balanced binary-search-tree `Expr`s** over
   numeric literals (comparisons via the kernel-accelerated `Nat.ble`/`Nat.beq`),
   so each lookup reduces in `O(log numProd)`. `prodLhsOf`/`prodRhsRevOf` delegate
   to them. The fields carry array-backed **defaults** (`fun i => prodLhs.getD i 0`),
   so legacy/hand-written `GenTables` literals (`MiniCalc`, `emitTables` output,
   the `partial` generators) keep working unchanged. `GenTables` lost its derived
   `Repr`/`ToExpr` (functions have neither); `build_tables%` now builds the literal
   field-by-field via `mkGenTablesExpr` (`toExpr` for data fields + synthesised
   trees for the two function fields). Result: L0 `actions` elaborates in ~1.5 s
   (was OOM); kernel `decide` certs on small grammars got faster too.
   Invariant `prodLhsFn i = prodLhs.getD i 0` (∀ `i < numProd`) is regression-tested.

2. **`Fin`-literal exhaustiveness wall (newly discovered).** With (1) making per-arm
   typing cheap, elaboration now *reaches* a second wall: Lean's equation compiler
   only proves a `Fin n` numeric-literal match exhaustive (using `isLt` to rule out
   `val ≥ n`) for **small `n`** — past ~15 arms it reports the out-of-range index as
   a "missing case" (verified: a bare `def f : Fin 21 → Nat | 0 => .. | 20 => ..`
   already fails; `Fin 11` is fine). This is independent of the tables/our fix.
   Solution: a trailing impossible arm `⟨_ + (numProd+1), h⟩ => elimOutOfRange h`,
   where `Gen.elimOutOfRange {α} {m K} (h : m + K < K) : α := absurd h (by omega)`
   turns the absurd bound into a value of any type, so the arm type-checks with no
   exhaustiveness reasoning. **The BNFC emitter must append this one arm to every
   generated dispatcher** (see `LEANMENHIR-SCALING-RESPONSE.md`).

Files: `Generator/Tables.lean` (`GenTables` fields + `prodLhsOf`/`prodRhsRevOf` +
`elimOutOfRange`), `Generator/BuildTables.lean` (`mkLookupTree`/`mkLookupLambda`/
`mkGenTablesExpr`, dropped `deriving ToExpr GenTables`), `Examples/CalcTemplate.lean`
& `Examples/StmCalc.lean` (now model the catch-all arm), new
`Examples/ScaleTest.lean` (21-production regression guard, kernel-`decide`-certified,
axioms `{propext, Quot.sound}`). Whole project builds (2987 jobs).

### Follow-up investigation (negative results — do not re-attempt)

BNFC reported L0 still builds slowly and asked about two further avenues. Both were
investigated and ruled out:

- **`ntType`/`termType` as the next wall (BNFC's hypothesis).** Falsified by
  controlled measurement: replacing the `Fin n → Type` literal matches with balanced
  jump-trees (a `type_lookup%` elaborator) cut the `actions` *type-checking* phase
  1.88s → 0.55s, but `actions` elaboration **still** exceeds ~2M heartbeats either
  way. The dominant cost is the **inherent per-arm reduction of the dependent
  dispatcher motive** (~few-k heartbeats × 256 arms ≈ 2–4M), which no amount of
  lookup-speedup removes. Conclusion: leave `ntType`/`termType` as plain matches;
  the BNFC emitter should simply set `maxHeartbeats` to ~4M (down from 16M). Per-arm
  cost is only a few seconds of *wall* time — it is not the build-time bottleneck.

- **Jump-tabling the validator tables to enable kernel `decide` at L0 scale (handoff
  §8-Q2).** A first attempt encoded the tables as nested-`cond` *functions*
  (`fun n => cond … cond …`); kernel `decide` on L0's `safeValidator` **blew up to
  68 GB**. Root cause (later pinned down): applying such a function beta-substitutes
  the key into the *entire* function body — an `O(tree size)` copy *per lookup* —
  which, over the validators' tens of thousands of lookups, exhausts memory. The
  `decide` *tactic* is also a dead end here for a *different* reason: it refuses to
  reduce custom recursive lookups at all (reports "stuck").

  **This was NOT, however, the final word — see the resolution below.** The earlier
  blanket claim that "kernel `decide` is infeasible regardless of representation" was
  wrong; it is the *cond-lambda* encoding + the `decide` *tactic* that fail, not
  kernel reduction per se.

### Resolution (2026-06-26): `native_decide` for L0; kernel-`rfl` `BTree` path kept as an experiment

Two things were finally measured directly (under a `systemd-run` memory cap), settling it:

- **`native_decide` is workable for L0** — the **shipping array-based** path
  (`b0390acd`) certifies `safeValidator` in **~3.2 min, under 32 GB** (`exit 0`); both
  certs ≈ ~6.4 min. The agent's ">15 min" was the *whole* `lake build` (certs +
  `actions` elaboration + codegen + Mathlib), which does finish. **No further
  LeanMenhir change is needed for the `native_decide` path.** Cost: the standard
  `Lean.ofReduceBool` compiler-trust axiom.

- **`BTree` does *not* help `native_decide`** (measured: `BTree` + `native_decide`
  L0 `safe` ≈ 4.6 min — ~1.4 min *slower* than array + `native_decide`). The O(n)
  penalty `BTree` removes is a **kernel-reduction** artifact (kernel `Array.getD`
  walks a backing `List`); in **compiled** code `Array.getD` is already O(1), whereas
  `BTree.find` is O(log n), and the `BTree` literal (≈2× the nodes) compiles slower.
  `BTree` pays off **only** on the kernel-`rfl` path.

- **Kernel `decide` *can* be made to work**, via `BTree` *data* (a balanced search
  tree as a shared literal) + `BTree.find` + `by rfl` (kernel defeq, since the
  `decide` tactic won't reduce `BTree.find`). `find` descends shared subterms in
  `O(log n)` with no key-substitution, so there is no beta-copy blow-up. L0
  `safeValidator` then certifies by **kernel `rfl`** (`exit 0`) — axioms
  `{propext, Quot.sound}`, no compiler trust — but at **~12.7 min and 24–60 GB**,
  i.e. ~4× slower and far heavier than the array + `native_decide` path.

**Decision:** ship the `native_decide` path (faster, lighter, already committed). The
`BTree` + `rfl` work is preserved as the experimental commit
`experiment(generator): BTree-data + kernel-rfl certificates` (jj change `vuvtlqru`)
for reference / future use if a kernel-only trust story is ever required. It is the
only kernel approach that *finishes* on L0; every other (array `O(n)` walks,
cond-lambda beta-copy) crashed or never completed.

Optional future lever (either path): make the **completeness** certificate optional
(it needs the large `items` table + a second cert); a soundness-only build skips both.

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
   - `Examples/StmCalc` — a **two-category** grammar (`Exp` and `Stm` as distinct
     AST types: `Program → Stm EOF; Stm → Exp ";"; Exp → Exp "+" Atom | Atom;
     Atom → NUM | "(" Exp ")"`) built through the **heterogeneous** bridge
      `Gen.automatonOfTablesTyped` (see below). SLR(1), 12 states, kernel `decide`
      certificates (`stmSafe`/`stmComplete` axioms = `{propext, Quot.sound}`), with
      `stm_parses`/`stm_unambiguous` corollaries and typed parse tests (`parseStm`
      returns a `Stm` directly). Tables come from `build_tables% grammar` (strategy
      C — generated at elaboration time, no hand-pasted literal).
   - `Examples/CalcTemplate` — the **emission template** for the BNFC backend: a
      calculator with precedence-by-coercion and parens, structured exactly as the
      backend will emit (grammar → `build_tables%` → `ntType`/`termType`/`actions`
      → automaton → token adapter → `parseString : String → Except String Exp`
      with `line:col` errors, via `LeanMenhir.Runtime`). Kernel-`decide` certified.

## Heterogeneous (typed) semantic bridge (DONE)

`Gen.automatonOfTables` keeps semantic values **monomorphic** — a single `Val`
type for every symbol — which forces an AST-producing front-end (BNFC) to encode
all categories in a tagged union, *project* it back out in each action, and
fabricate `Inhabited` defaults for the never-reached projection branches.

`Gen.automatonOfTablesTyped` (in `Generator/Tables.lean`) instead gives every
symbol its **own** type:
- `symbol_semantic_type := symTypeOf g ntType termType` — `termType t` for terminal
  `t`, `ntType n` for nonterminal `n`.
- `Token := (t : Fin (numTerm+1)) × termType t` (a `Σ`-pair); `token_term :=
  Sigma.fst`, `token_sem := Sigma.snd`.
- `prod_action := actions`, where `actions` is the **dependent dispatcher**
  `(p : Fin (numProd+1)) → arrowsRight (ntType (prodLhsOf g p)) ((prodRhsRevOf g
  p).map symType)` — each branch an ordinary typed action building the AST
  directly (no union, no projection).

Key facts established by the prototype/port:
- The verified interpreter and the safety/completeness validators are generic over
  `symbol_semantic_type`, so they accept the typed automaton **unchanged** — zero
  proof changes; same axiom sets as the monomorphic path.
- The dependent dispatcher elaborates with plain `Fin` numeral patterns (`| 0 =>
  … | n => …`); Lean handles exhaustiveness and reduces each branch's expected
  type to the concrete arrow type (`prodLhsOf`/`prodRhsRevOf` are shared between
  the field defs and the `actions` parameter type so they are definitionally
  equal).
- **No `Inhabited` for any AST category.** The only values conjured from nothing
  are `()` at `Unit`: the dummy padding production (`ntType dummyNt := Unit`) and
  the `Unit`-payload terminals (keywords/punctuation/EOF). Value-carrying tokens
  (e.g. `NUM : Nat`) are always supplied by the lexer.
- Constraint: the dependent `actions` requires the production data of `g` to
  *reduce*, i.e. `g` is a **concrete `GenTables` literal** (the emitted-tables /
  kernel-`decide` path), not an opaque `partial buildTablesSLR` result. The
  `build_tables%` elaborator (below) satisfies this in a single build phase.

This is the highest-leverage simplification for the eventual BNFC `--lean`
backend: it emits typed actions that construct the BNFC AST directly, with no
`Val`-union / projection / `Inhabited`-deriving plumbing.

## `build_tables%` elaborator — strategy C (DONE)

`Generator/BuildTables.lean` provides a term elaborator `build_tables% grammar`
that runs the untrusted generator `Grammar0.buildTablesSLR` **at elaboration
time** (via `Lean.Meta.evalExpr`, wrapped in the standard `unsafe` +
`@[implemented_by]`/`opaque` pattern) and splices the result back as a **concrete
`GenTables` literal** using `deriving ToExpr` on `GSym`/`GLookahead`/`GAction`/
`GenTables`.

This resolves the "tables must reduce" constraint of the heterogeneous bridge in
a **single `lake build` phase** (no separate codegen executable, no hand-pasted
literal): `def stmTables := build_tables% grammar`. The spliced literal reduces
by `rfl`, the heterogeneous dispatcher typechecks against it, and **kernel
`decide`** certifies `safe`/`complete` — the elaborator itself adds **no axioms**
(it only produces a literal). `Examples/StmCalc` uses this flow. The generator
stays untrusted: a buggy table is rejected by the validator, never accepted.

This is the chosen table-generation strategy for the BNFC backend (vs (A)
reimplement SLR in Haskell, or (B) a two-phase Lean codegen tool).

## Parse driver runtime + BNFC emission template (DONE)

`LeanMenhir/Runtime.lean` is a small **grammar-agnostic** driver over the verified
`Main.parse`:
- `fuelFor n` — a step-budget exponent generous enough for `n` tokens (too-small
  fuel only yields a `Timeout`, never an unsound result).
- `parseList init hsafe eof toks onFail onTimeout` — pads the finite token list
  with `Stream'.const eof` and projects `ParseResult` into `Except E`.
- `parseWith … adapt …` — additionally converts each external (lexer) token via
  `adapt : Tok → Except E A.Token`.

To let errors report source positions, `automatonOfTablesTyped` gained a per-token
`Info` slot: `Token := Info × (Σ t, termType t)` (the verified parser ignores
`Info`; actions are unchanged). The driver's `onFail` receives the failing
lookahead token, so the caller pulls a `Position` out of `tok.1`.

`Examples/CalcTemplate.lean` is the **emission template** — the exact shape the
BNFC backend will emit for a precedence calculator: grammar → `build_tables%` →
`ntType`/`termType`/`actions` (coercions are identity actions; `Exp`/`Exp1`/`Exp2`
all map to the AST type `Exp`) → automaton (`Info := Position`) → a
`TokenKind → terminal` adapter → `parseString : String → Except String Exp` with
`line:col` errors. Kernel-`decide` certified; precedence/associativity/parens and
error positions verified by `native_decide`/`#eval`. This pins the contract for
the Haskell emitter.

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
- BNFC `--lean` backend integration to emit `Grammar0` from `.cf` files. The Lean
  side is now ready: heterogeneous bridge (`automatonOfTablesTyped`), `build_tables%`
  (strategy C), the `LeanMenhir.Runtime` driver, and `Examples/CalcTemplate` as the
  exact emission shape. Remaining (Haskell side): the `Grammar0` + typed-action
  emitter (rule zoo: coercions, lists, `define`), the `Reg → Lean` lexer compiler
  (the large independent piece — unblocks user `token`s), multi-entrypoint support
  (cheap: one automaton per entrypoint), and conflict diagnostics. Position/error
  plumbing is **done** (per-token `Info` slot + driver `onFail`).
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
