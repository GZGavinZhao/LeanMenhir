# Handoff: Porting `coq-menhirlib` to a Fully Verified Lean 4 LR(1) Parser

**Project codename (suggested):** `LeanMenhir` (a.k.a. a verified LR(1) parser
interpreter + validator for Lean 4).

**One-line goal:** Reproduce, in Lean 4, the verified LR(1) parser library that
Menhir emits for Coq (`coq-menhirlib`), including machine-checked **soundness**,
**completeness**, and **unambiguity** theorems, so that BNFC (and others) can
generate parsers whose correctness is proved in Lean.

---

## 0. TL;DR feasibility verdict

**Feasible, but it is a real verification project, not a mechanical transliteration.**

- The **definitions** (grammar interface, automaton/table interface, the
  dependently-typed `parse_tree` semantics, the interpreter `step`/`parse` loop,
  the validators) port from Coq to Lean 4 almost 1:1. Lean 4 natively supports
  everything used: indexed inductive families, dependent functions, sigma types
  carrying equality proofs, decidable equality, finiteness.
- The **proofs** do **not** port mechanically. The Coq sources are written in
  **SSReflect** tactic style (`Coq.ssr.ssreflect`); Lean 4 has a completely
  different tactic language. The lemma/structure roadmap transfers, but every
  proof script is re-done in Lean. This is the bulk of the effort.
- The hardest single artifact is `Interpreter_complete.v` (824 LOC, mostly
  proof). **Soundness alone** (the safety-critical property) is much smaller and
  is the recommended MVP.

Rough effort: a skilled Lean 4 / Mathlib prover (or a well-supervised agent with
fast proof-iteration tooling) should plan on the order of weeks-to-a-couple-months
for the full set of theorems; the soundness MVP (M0–M3 below) is a much smaller
slice and delivers most of the practical value.

---

## 1. Background: where this comes from and why

This came out of work on the **BNFC Lean 4 backend** (`bnfc --lean`). BNFC's
existing Lean backend generates a hand-rolled recursive-descent parser
(`source/src/BNFC/Backend/Lean/CFtoLeanPar.hs`). That parser is effectively a
**PEG**: it tries a category's alternatives in grammar order and commits to the
first success, with no longest-match and no global backtracking. This is
**incorrect** for ordinary unambiguous LALR grammars — e.g. variable-arity
instructions in an assembly language (`Instr ::= Ident | Ident Op | Ident Op "," Op`)
either fail or are **silently mis-parsed** (`jmp loop` parses as two separate
0-operand instructions). Every *other* BNFC backend avoids this by delegating to
a real **LALR table-driven generator**: Haskell→Happy, OCaml→ocamlyacc/Menhir,
C→Bison, Java→CUP.

The "most robust" fix is therefore an LR(1)/LALR table-driven parser. The key
precedent that makes a Lean version attractive: **Menhir already targets a
dependently-typed functional proof assistant — Coq** — via its `--coq` backend
(Jacques-Henri Jourdan, 2011), and that verified parser is used in production by
**CompCert**, the formally verified C compiler. Coq is in the same family as
Lean 4, so the artifact we want already exists in a near-cousin language.

References (papers):
- Jourdan, Pottier, Leroy. *Validating LR(1) Parsers.* ESOP 2012.
  https://xavierleroy.org/publi/validated-parser.pdf
- CompCert's parser blog: https://cambium.inria.fr/blog/verifying-a-parser-for-a-c-compiler/

**The architectural insight to preserve (this is the whole point):** the LR
table **generator is left untrusted**. A separate **verified validator** checks
that the generated automaton is consistent with the grammar; a **verified
interpreter** runs validated tables. Soundness holds *whenever the validator
accepts the tables*, regardless of bugs in the generator. You never have to
verify the (large, fiddly) LR table-construction algorithm.

---

## 2. What you are porting

The source is **`coq-menhirlib`**, already cloned in this repo at:

```
refs/menhir/coq-menhirlib/src/
```

Read these in this order. Sizes are total lines (proofs included):

| Coq file | LOC | Role | Port difficulty |
|---|---|---|---|
| `Alphabet.v` | 249 | Typeclass for finite, decidably-equal, linearly-ordered types (terminals, nonterminals, states, productions) + list/finite lemmas | Medium (foundational; lots of small lemmas) |
| `Grammar.v` | 161 | Grammar interface: `symbol = T term | NT nt`, `symbol_semantic_type`, productions (`prod_lhs`, `prod_rhs_rev`, `prod_action`), tokens, and the **`parse_tree` / `parse_tree_list` dependent families** + `pt_sem`, `pt_size` | Medium (definitions only; dependent families) |
| `Automaton.v` | 162 | Table interface: `action_table : state → action`, `goto_table`, `Shift_act`/`Reduce_act`/`Fail_act`, plus validation annotations (`items_of_state`, `past_symb_*`, `past_state_*`, `nullable_nterm`, `first_nterm`) | Medium (dependent `Shift_act` carries an eq proof) |
| `Validator_classes.v` | 73 | `IsValidator (P : Prop) (b : bool)` reflection typeclass + combinators | Easy–Medium |
| `Validator_safe.v` | 233 | Safety validator `is_safe : unit → bool` + proof it implies the interpreter invariants | **Medium–Hard (soundness-critical)** |
| `Interpreter.v` | 463 | The interpreter: `pop`, `reduce_step`, `step`, `parse` (fuel-based). **~30 lines of algorithm, ~430 lines of invariant proof** | Medium (algo) / Hard (invariants) |
| `Interpreter_correct.v` | 174 | **Soundness**: a successful parse yields a real `parse_tree` with matching semantics | Hard |
| `Validator_complete.v` | 393 | Completeness validator `is_complete : unit → bool` + proofs | Hard |
| `Interpreter_complete.v` | 824 | **Completeness**: if a parse tree exists, the parser finds it (within fuel) | **Hardest** |
| `Main.v` | 77 | Ties it together; states the 3 user-facing theorems | Easy |

### The three theorems (from `Main.v`, the definition of "done")

```coq
(* Soundness *)
Theorem parse_correct (safe : safe_validator () = true) init log_n_steps buffer :
  match parse safe init log_n_steps buffer with
  | Parsed_pr sem buffer_new =>
      exists word (pt : parse_tree (NT (start_nt init)) word),
        buffer = (word ++ buffer_new) /\ pt_sem pt = sem
  | _ => True
  end.

(* Completeness *)
Theorem parse_complete (safe : safe_validator () = true)
    init log_n_steps word buffer_end :
  complete_validator () = true ->
  forall tree : parse_tree (NT (start_nt init)) word,
  match parse safe init log_n_steps (word ++ buffer_end) with
  | Fail_pr => False
  | Parsed_pr sem_res buffer_end_res =>
      sem_res = pt_sem tree /\ buffer_end_res = buffer_end
      /\ pt_size tree <= 2 ^ log_n_steps
  | Timeout_pr => 2 ^ log_n_steps < pt_size tree
  end.

(* Unambiguity (a corollary of soundness+completeness) *)
Theorem unambiguity : safe_validator () = true -> complete_validator () = true ->
  inhabited token -> forall init word (t1 t2 : parse_tree (NT (start_nt init)) word),
  pt_sem t1 = pt_sem t2.
```

`parse` is total via a **fuel** parameter `log_n_steps` (budget `2^log_n_steps`
steps); running out yields `Timeout_pr`. Keep this design in Lean (it matches the
completeness statement and sidesteps well-founded-recursion proofs).

### How tables are produced (the untrusted half)

Menhir's OCaml `src/RocqBackend.ml` (568 LOC, in `refs/menhir/`) reads a
Coq-flavored grammar (`.vy`: productions + Coq semantic actions, see the worked
example `refs/menhir/demos/rocq-minicalc/Parser.vy`) and **emits a `Parser.v`**
that instantiates `Automaton.T` with concrete tables, then applies
`MenhirLib.Main.Make`. Running `safe_validator ()` (via `vm_compute`/`decide`)
discharges the soundness precondition.

You do **not** need to port `RocqBackend.ml` to start. To get end-to-end test
cases, run `menhir --coq` on a `.vy` and **translate the emitted Coq table data
into Lean syntax** (it is plain inductive enumerations + table functions — a
mostly syntactic translation, scriptable). A native generator (or BNFC
integration) can come later.

---

## 3. Target architecture in Lean 4

Standalone Lake package. Suggested layout (mirror the Coq module names so the
mapping stays obvious):

```
LeanMenhir/
  lakefile.toml            -- or lakefile.lean
  lean-toolchain           -- pin a specific Lean 4 release
  LeanMenhir.lean          -- root: re-exports
  LeanMenhir/Alphabet.lean
  LeanMenhir/Grammar.lean
  LeanMenhir/Automaton.lean
  LeanMenhir/Validator/Classes.lean
  LeanMenhir/Validator/Safe.lean
  LeanMenhir/Validator/Complete.lean
  LeanMenhir/Interpreter.lean
  LeanMenhir/Interpreter/Correct.lean
  LeanMenhir/Interpreter/Complete.lean
  LeanMenhir/Main.lean       -- the 3 theorems, user-facing `parse`
  examples/MiniCalc/...      -- ported rocq-minicalc, end-to-end
  test/...
```

### Coq construct → Lean 4 construct (decide these up front)

1. **Module functors (`Module Type T` + `Module Make(Import A:Automaton.T)`).**
   Lean has no module functors. This is the single most important structural
   decision. Recommended approach:
   - Represent each Coq `Module Type` as a Lean **`structure`** (or `class`)
     bundling the parameters and operations (e.g. `structure Grammar where
     terminal : Type; ... prod_action : ...`). Because fields are dependent
     (`symbol_semantic_type : symbol → Type`, etc.), these are large dependent
     structures — fine in Lean.
   - Replace `Module Make(A)` definitions with plain `def`s/`theorem`s that take
     the structure as an argument, or use `variable (G : Grammar)` /
     `variable [Automaton G]` in a `section`. Pick one convention and apply it
     everywhere.
   - Caution: deeply dependent bundled structures can get awkward with universe
     levels and with `Type`-valued fields. Prototype `Grammar`/`Automaton` as
     structures first and make sure `parse_tree` and the interpreter typecheck
     against them before investing in proofs.

2. **`Alphabet` typeclass.** It's: decidable equality + a `compare` giving a
   strict linear order + finiteness (`all_list` enumerating every element with a
   proof it's exhaustive). Two options:
   - **Use Mathlib**: `DecidableEq`, `LinearOrder`, `Fintype`. You get a large
     lemma library for free. Cost: Mathlib is a heavy dependency (build time,
     version churn) — but for a *proof* library that is usually acceptable.
   - **Self-contained**: define your own `class Alphabet (α) where deq; compare;
     all : List α; mem_all : ∀ a, a ∈ all` and prove the handful of list lemmas
     you need. Keeps the package dependency-light (consistent with the BNFC Lean
     backend's "no external deps" philosophy) at the cost of re-proving basics.
   - **Recommendation:** start with Mathlib to move fast on proofs; revisit
     de-Mathlib-ing only if the dependency becomes a problem for downstream use.
     Record this as an explicit decision.

3. **Dependent types & coercions of equality.** Coq's `eq_rect`, `cast`,
   `eq_refl`, and `existT` map to Lean's `Eq.mpr` / `▸` (`Eq.subst`) / `cast` /
   `⟨_, _⟩` for `Sigma`/`Subtype`. The `Shift_act`/`goto_table` proofs
   (`T term = last_symb_of_non_init_state s`) become `Eq` fields in the data and
   `▸`-rewrites in the interpreter. Expect some friction; isolate it.

4. **`Program Instance` / obligations** (in `Alphabet.v`, `Grammar.v`,
   `Automaton.v`). In Lean, fill instance proof fields directly
   (`instance : Alphabet α where ... := by ...`). The obligation tactics become
   ordinary Lean tactic blocks.

5. **SSReflect proofs (`=>`, `//`, `by`, `move`, `rewrite`, `case`).** Rewrite in
   Lean 4 tactic mode. Useful analogues: `intro`/`rintro`, `simp`, `rw`,
   `cases`/`rcases`, `induction`, `omega` (for the `Arith`/`Nat` reasoning in the
   completeness proofs and fuel bounds), `decide`, `constructor`, `exact?`/
   `apply?` for lemma search. Mathlib's `List` and `Nat.pow` lemmas cover much of
   what `Interpreter_complete.v` needs.

6. **The `IsValidator P b` pattern** (`Validator_classes.v`) is reflection
   between a `Prop` and a decidable `bool` check, with composable instances. It
   ports cleanly as a Lean `class IsValidator (P : Prop) (b : Bool)` with
   instances; consider whether `Decidable P` + Mathlib's `decide` machinery can
   replace part of it (it may simplify things, but staying close to the Coq
   structure de-risks the proofs).

7. **Termination.** Keep the **fuel** (`log_n_steps`, `2^n`) interpreter. Don't
   try to switch to well-founded recursion — the completeness theorem is stated
   in terms of the step budget, and fuel keeps `parse` obviously total.

8. **Executability.** The Coq version is extracted to OCaml; here the Lean
   `parse` should be directly runnable. Ensure the table data and `parse` compile
   to efficient code (avoid `Prop`-valued computation on the hot path; the
   dependent eq-proofs should erase). Validate `safe_validator () = true` at
   build/run time with `decide` or `native_decide`.

---

## 4. Deliverables & milestones

Each milestone is independently buildable and reviewable. "Done" = builds with
**zero `sorry`** (for the proof milestones) and CI green.

- **M0 — Skeleton + Alphabet.** Lake package, toolchain pin, `Alphabet.lean`
  (finite/ordered/decidable infra) with its lemmas proved. Decide Mathlib-or-not
  here. *DoD:* `Alphabet.lean` compiles, no `sorry`.

- **M1 — Grammar + Automaton interfaces + semantics (definitions only).**
  `Grammar.lean` (symbols, productions, `parse_tree`/`parse_tree_list`,
  `pt_sem`, `pt_size`), `Automaton.lean` (action/goto tables, annotations).
  *DoD:* compiles; a trivial hand-written grammar instance typechecks.

- **M2 — Interpreter (executable, unverified).** `Interpreter.lean`: `pop`,
  `reduce_step`, `step`, `parse` with fuel and `parse_result`
  (`Parsed | Fail | Timeout`). *DoD:* you can hand-write a tiny automaton and
  `#eval parse ...` on a token list and get the right tree. No proofs yet.

- **M3 — Soundness (the MVP).** `Validator/Classes.lean`, `Validator/Safe.lean`,
  `Interpreter/Correct.lean`, and the `parse_correct` theorem in `Main.lean`.
  *DoD:* `parse_correct` proved, no `sorry`. **This is the high-value deliverable**
  — it guarantees the parser never accepts a string that isn't in the language
  (given the safe validator passed).

- **M4 — Completeness + unambiguity (stretch / hardest).**
  `Validator/Complete.lean`, `Interpreter/Complete.lean`, `parse_complete` and
  `unambiguity` in `Main.lean`. *DoD:* both proved, no `sorry`.

- **M5 — End-to-end example.** Port `refs/menhir/demos/rocq-minicalc` to Lean:
  ingest its tables (translate `menhir --coq` output to Lean), evaluate
  `safe_validator () = true` by `decide`/`native_decide`, and parse real input
  to an AST via an executable. *DoD:* `lake exe minicalc` parses `1 + 2 * 3`
  correctly; the safety precondition is discharged by computation.

- **M6 — (Optional) Table generator / BNFC integration.** Either a native Lean/
  Haskell LR(1) generator emitting the Lean tables, or wire BNFC's `--lean`
  backend to emit `Automaton`-instance tables + per-production semantic actions
  (BNFC already computes these for Happy in
  `source/src/BNFC/Backend/Haskell/CFtoHappy.hs:170`, `constructRule`). *DoD:*
  `bnfc --lean Foo.cf` produces a project that builds on top of `LeanMenhir`.

**Recommended stopping point if time-boxed:** M3 + M5 (sound, runnable, with a
real example). M4 is a meaningful research contribution but can follow later.

---

## 5. Testing & validation strategy

- **Differential testing against Coq:** for a given `.vy`, generate the Coq
  parser (`menhir --coq`) AND the Lean tables; check both accept/reject the same
  inputs and produce structurally identical ASTs. The minicalc demo is the
  starter; add the assembly grammar from the BNFC investigation
  (`tmp/asm2/Asm.cf`) as a second case since it exercises the prefix/longest-match
  behavior the old PEG got wrong.
- **`native_decide` the validators** on each example automaton so the soundness
  precondition is machine-checked, not assumed.
- **Property tests** (Lean `Plausible`/`SlimCheck` if used, or hand-rolled): for
  random token strings, `parse` never crashes (totality) and round-trips through
  the pretty-printer where applicable.
- **No-`sorry` gate** in CI (`grep`/`lake` check that no `sorry`/`admit`/`native_decide`
  leaks into the *trusted* core — `native_decide` is fine for *examples* but
  should not appear inside the library proofs).

---

## 6. Risks & mitigations

| Risk | Mitigation |
|---|---|
| Module-functor → structure translation gets unwieldy with dependent `Type`-valued fields | Prototype `Grammar`+`Automaton`+`parse_tree`+interpreter (M1–M2) **before** any proofs; lock the structuring convention early |
| `Interpreter_complete.v` (824 LOC) proof is very hard | Treat M4 as stretch; ship M3 (soundness) first. Soundness is the safety property that matters most |
| ssreflect idioms have no 1:1 Lean tactic | Use the lemma *structure* as the map, re-prove with `simp`/`omega`/`rcases`/Mathlib; budget time for this, it's the main cost |
| Mathlib dependency churn / build time | If it bites, the `Alphabet` infra is the only hard dependency point; it can be made self-contained |
| Dependent eq-proof plumbing (`eq_rect`/`▸`) clutters the interpreter and blocks `#eval` | Keep proofs in `Prop`, ensure they erase; test executability at M2 before adding invariants |
| Lean version drift | Pin `lean-toolchain`; the Coq sources are stable, so the moving target is only Lean/Mathlib |

---

## 7. Licensing (important)

`coq-menhirlib` is **LGPL-3.0-or-later** (see
`refs/menhir/coq-menhirlib/LICENSE` and the per-file headers). A Lean port is a
**derivative work**. Unless relicensing permission is obtained from the authors
(Inria/CNRS; Jacques-Henri Jourdan, François Pottier, Xavier Leroy), the Lean
port must be distributed under **LGPL-3.0-or-later**, retain attribution, and
note the original authorship. Confirm this is compatible with where the code will
live (note: BNFC itself is BSD-3-clause, so this library likely must be a
*separate* LGPL package that BNFC's generated code links against, not vendored
into BNFC's BSD tree). **Resolve the license question before publishing.**

---

## 8. Concrete first session

1. Read, in order: `Main.v`, `Grammar.v`, `Automaton.v`, `Interpreter.v`
   (focus on `step`/`reduce_step`/`pop`/`parse`, skip the proofs), then
   `Validator_safe.v` and `Interpreter_correct.v`. All under
   `refs/menhir/coq-menhirlib/src/`.
2. Skim `refs/menhir/demos/rocq-minicalc/` (`Parser.vy`, generated `*.v`,
   `MiniCalc.v`) to see the end-to-end shape.
3. Decide: Mathlib or self-contained `Alphabet`? Structures-with-`variable` vs
   bundled-class for the "module functor" pattern? Write these decisions down.
4. Build M0 + M1 (definitions only). Get `parse_tree` and a trivial `Automaton`
   instance to typecheck. Do **not** start proofs until the dependent
   definitions are solid.
5. Then M2 (executable interpreter) and confirm `#eval` works on a hand-built
   automaton.

Only after M0–M2 typecheck and run should you begin the soundness proofs (M3).

---

## 9. Open decisions to record early

- [ ] Mathlib dependency: yes (faster proofs) or no (lighter, self-contained)?
- [ ] Module-type encoding: bundled `structure`/`class` vs `section`+`variable`?
- [ ] Fuel vs well-founded recursion for `parse` (recommended: **fuel**).
- [ ] Where the package lives + final license (LGPL-3.0+ unless relicensed).
- [ ] Scope: soundness-only (M3) vs full (M4) for v1?
- [ ] Table ingestion for v1: translate `menhir --coq` output, or native generator?

---

## 10. Pointers recap (all local)

- Coq library to port: `refs/menhir/coq-menhirlib/src/*.v`
- Coq table generator (reference, do not need to port initially):
  `refs/menhir/src/RocqBackend.ml`
- Worked end-to-end example: `refs/menhir/demos/rocq-minicalc/`
- BNFC Lean backend (the consumer/motivation):
  `source/src/BNFC/Backend/Lean/` and its `NOTES.md`
- Test grammar that breaks the current PEG backend: `tmp/asm2/Asm.cf`
- Paper: *Validating LR(1) Parsers* (Jourdan, Pottier, Leroy), ESOP 2012.
