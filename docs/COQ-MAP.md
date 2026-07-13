# Coq ↔ Lean traceability map

LeanMenhir is a port of `coq-menhirlib` (see `refs/menhir/coq-menhirlib/src/`).
This table maps the Coq development to its Lean counterparts so cross-checking
stays one lookup away. Structure/field names deliberately keep the exact Coq
spellings (`prod_rhs_rev`, `last_symb_of_non_init_state`, …) — they are
load-bearing for this table.

## Files

| Coq | Lean | Notes |
|---|---|---|
| `Alphabet.v` | `LeanMenhir/Spec/Alphabet.lean` | `comparison` ↦ `Ordering`; `Finite.all_list` ↦ `Enumerable.allList` (computable) |
| `Grammar.v` | `LeanMenhir/Spec/Grammar.lean` | `Grammar.T` module type ↦ `structure Grammar`; `parse_tree`/`parse_tree_list` ↦ `ParseTree G`/`ParseTreeList G` with constructors `leaf`/`node`/`nil`/`cons` (ex `Terminal_pt`/`Non_terminal_pt`/`Nil_ptl`/`Cons_ptl`) |
| — | `LeanMenhir/Spec/Language.lean` | no Coq counterpart: named language membership (`Grammar.Derives`, `G.language`) |
| `Automaton.v` | `LeanMenhir/Machine/Automaton.lean` | `Automaton.T` (extends grammar via functor) ↦ `structure Automaton (G : Grammar)` (explicit grammar parameter); adds `goto_enum`(+`_complete`) for sparse validator iteration |
| `Validator_classes.v` | `LeanMenhir/Correctness/Classes.lean` | Coq `IsValidator`+`Derive` reflection ↦ hand-written booleans + soundness lemmas |
| `Validator_safe.v` | `LeanMenhir/Correctness/Safe.lean` | `safe` ∧-chain ↦ `structure Safe (A) : Prop`; `is_safe` ↦ `isSafe`/`Safe.check`; `safe_is_validator` ↦ `Safe.of_check` |
| `Validator_complete.v` | `LeanMenhir/Correctness/Complete.lean` | `complete` ↦ `structure Complete (A) : Prop`; AVL `TerminalSet`/`FMap` ↦ lists over `items_of_state` |
| `Interpreter.v` | `LeanMenhir/Machine/Interpreter.lean` | `Stream` buffer ↦ `Buf` (`LeanMenhir/Spec/Buffer.lean`, O(1) head/tail, denotation `get`) |
| `Interpreter_correct.v` | `LeanMenhir/Correctness/Sound.lean` | buffer equality ↦ pointwise `get`-equality |
| `Interpreter_complete.v` | `LeanMenhir/Correctness/CompleteProof.lean` | same zipper proof architecture |
| — | `LeanMenhir/Correctness/Congr.lean` | no Coq counterpart: interpreter extensionality in the buffer (leak-1 fix; Coq streams don't need it) |
| — | `LeanMenhir/Correctness/Anchored.lean` | no Coq counterpart: EOF-anchoring, exact-consumption (leak-3 fix) |
| `Main.v` | `LeanMenhir/Main.lean` | plus equation-hypothesis primaries (`parse_sound`, `parse_complete_parsed`, …) |
| — | `LeanMenhir/Guarantees.lean` | no Coq counterpart: the review surface |
| — | `LeanMenhir/Runtime.lean`, `Generator/*` | no Coq counterpart: executable driver and in-Lean (untrusted) table generator; in Coq these roles are played by menhir's `--coq` backend emitting the tables. `Generator/Grammar0.lean`+`Derives0.lean`: the human-written grammar, its definitional interpretation (`toGrammar`), and the textbook `Grammar0.Derives` + transport |

## Key declarations

| Coq | Lean |
|---|---|
| `parse_tree` / `parse_tree_list` | `ParseTree G` / `ParseTreeList G` |
| `Terminal_pt` / `Non_terminal_pt` | `ParseTree.leaf` / `ParseTree.node` |
| `Nil_ptl` / `Cons_ptl` | `ParseTreeList.nil` / `ParseTreeList.cons` |
| `pt_sem` / `ptl_sem` / `pt_size` / `ptl_size` | `ptSem` / `ptlSem` / `ptSize` / `ptlSize` |
| `symbol_semantic_type`, `prod_lhs`, `prod_rhs_rev`, `prod_action`, `token_term`, `token_sem` | `Grammar` fields, same names |
| `last_symb_of_non_init_state`, `start_nt`, `action_table`, `goto_table`, `past_symb_of_non_init_state`, `past_state_of_non_init_state`, `items_of_state`, `nullable_nterm`, `first_nterm` | `Automaton` fields, same names |
| `safe` / `is_safe` / `safe_is_validator` | `Safe` / `Safe.check` (= `isSafe`) / `Safe.of_check` (= `safe_is_validator`) |
| `complete` / `is_complete` / `complete_is_validator` | `Complete` / `Complete.check` (= `isComplete`) / `Complete.of_check` |
| `state_has_future`, `future_of_prod` | `stateHasFuture`, `futureOfProd` (= `List.drop` of forward RHS) |
| `pop`, `step`, `parse_fix`, `parse` | `pop`, `step`, `parseFix`, `parse` |
| `step_result` / `parse_result` | `StepResult A init` / `ParseResult A R` |
| `word_has_stack_semantics` | `WordHasStackSemantics` |
| `pt_zipper` / `pt_dot` / `next_ptd` | `PtZipper` / `PtDot` / `nextPtd` |
| `Main.parse_correct` | `Main.parse_correct` (match-shaped) / `Main.parse_sound` (primary) |
| `Main.parse_complete` | `Main.parse_complete` (match-shaped) / `Main.parse_complete_parsed`+`parse_never_rejects`+`parse_timeout_bound` (primaries) |
| `Main.unambiguity` (`inhabited token`) | `Main.unambiguity` (`[Nonempty G.Token]`) |

Regenerate the declaration table by grepping for `(Coq \`` docstring tags:
`rg -o "\(Coq \`[^\`]+\`\)" LeanMenhir --glob '*.lean' | sort -u`.
