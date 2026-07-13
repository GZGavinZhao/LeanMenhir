/-
A two-category end-to-end example demonstrating the **heterogeneous** semantic
bridge (`Gen.automatonOfTablesTyped`).

Unlike `MiniCalc` (whose every symbol has the single value type `Expr`), this
grammar has two genuinely distinct AST categories — expressions and statements:

    Program → Stm EOF
    Stm     → Exp ";"
    Exp     → Exp "+" Atom | Atom
    Atom    → NUM | "(" Exp ")"

Each symbol carries its *own* type: `NUM` carries a `Nat`, every other terminal
carries `Unit`, `Exp`/`Atom` carry `Exp`, and `Program`/`Stm` carry `Stm`. The
semantic actions are ordinary typed functions that build the AST directly — note
in particular that the action for `Stm → Exp ";"` *consumes* an `Exp` and
*produces* a `Stm`. There is **no** tagged-union `Val` type, **no** projection,
and **no** `Inhabited` instance for any AST category: the only values conjured
out of nothing are `()` at `Unit` (keyword/EOF payloads and the dummy production).

The LR(1) tables (`stmTables`, SLR(1), 12 states) are produced from `grammar` by
the untrusted generator **at elaboration time** via the `build_tables%`
elaborator (strategy C) and certified here by the verified validators using
**kernel `decide`** (no `native_decide`/compiler-trust axiom).

LGPL-3.0-or-later (derivative of coq-menhirlib).
-/
import LeanMenhir.Generator.BuildTables

namespace LeanMenhir.Examples.StmCalc

open LeanMenhir LeanMenhir.Gen LeanMenhir.Buf

/-! ### The two AST categories -/

/-- Expressions. -/
inductive Exp where
  | num : Nat → Exp
  | add : Exp → Exp → Exp
deriving DecidableEq, Repr, BEq

/-- Statements (a distinct category from `Exp`). -/
inductive Stm where
  | sExp : Exp → Stm
deriving DecidableEq, Repr, BEq

/-! ### Grammar + generated tables

Terminals: PLUS=0 SEMI=1 LPAREN=2 RPAREN=3 EOF=4 NUM=5.
Nonterminals: Program=0 Stm=1 Exp=2 Atom=3. -/

/-- The source grammar (for documentation / regeneration of `stmTables`). -/
def grammar : Grammar0 where
  numTerm := 6
  numNonterm := 4
  start := 0
  eof := 4
  prods := #[
    (0, #[.nonterm 1, .term 4]),                 -- Program → Stm EOF
    (1, #[.nonterm 2, .term 1]),                 -- Stm → Exp SEMI
    (2, #[.nonterm 2, .term 0, .nonterm 3]),     -- Exp → Exp PLUS Atom
    (2, #[.nonterm 3]),                          -- Exp → Atom
    (3, #[.term 5]),                             -- Atom → NUM
    (3, #[.term 2, .nonterm 2, .term 3])         -- Atom → LPAREN Exp RPAREN
  ]

/-- The SLR(1) tables, computed from `grammar` **at elaboration time** by the
untrusted generator and spliced in as a concrete literal via the `build_tables%`
elaborator (strategy C — single-phase build, kernel-`decide`-friendly). -/
def stmTables : Gen.GenTables := build_tables% grammar

/-- Production lookups: the `build_tables%` jump trees, with their agreement to
`grammar.prods` certified by **kernel `rfl`** (intrinsic faithfulness). -/
@[reducible] def stmLk : Gen.ProdLookup grammar :=
  Gen.ProdLookup.ofTables grammar stmTables (by rfl)

/-! ### Heterogeneous semantic types and actions -/

/-- Per-nonterminal AST type: `Exp`=2 and `Atom`=3 carry `Exp`; `Program`=0 and
`Stm`=1 carry `Stm`; the dummy nonterminal `4` carries `Unit`. -/
def ntType : Fin (grammar.numNonterm + 1) → Type
  | 2 => Exp
  | 3 => Exp
  | 4 => Unit
  | _ => Stm

/-- Per-terminal payload type: `NUM`=5 carries a `Nat`; every other terminal
(keywords, punctuation, EOF, dummy) carries `Unit`. -/
def termType : Fin (grammar.numTerm + 1) → Type
  | 5 => Nat
  | _ => Unit

/-- The semantic actions, each in its *true* curried type (arguments in
reverse-RHS order). No `Val`, no projection, no `Inhabited`. -/
def actions : (p : Fin (grammar.prods.size + 1)) →
    arrowsRight (grammar.symType0 ntType termType (.NT (grammar.prodLhs0 stmLk p)))
                ((grammar.prodRhsRev0 stmLk p).map (grammar.symType0 ntType termType))
  | 0 => fun (_ : Unit) (s : Stm) => s                            -- Program → Stm EOF
  | 1 => fun (_ : Unit) (e : Exp) => Stm.sExp e                   -- Stm → Exp ";"  (Exp ↦ Stm)
  | 2 => fun (a : Exp) (_ : Unit) (e : Exp) => Exp.add e a        -- Exp → Exp "+" Atom
  | 3 => fun (a : Exp) => a                                       -- Exp → Atom
  | 4 => fun (n : Nat) => Exp.num n                               -- Atom → NUM   (Nat ↦ Exp)
  | 5 => fun (_ : Unit) (e : Exp) (_ : Unit) => e                 -- Atom → "(" Exp ")"
  | 6 => ()                                                       -- dummy production
  | ⟨_ + 7, h⟩ => elimOutOfRange h                                -- impossible (numProd+1 = 7)

/-- The verified grammar — a **definitional function of `grammar`** (D9): the
theorems below quantify over exactly the `Grammar0` above, not over anything the
untrusted generator produced. -/
@[reducible] def stmGrammar : Grammar :=
  grammar.toGrammarTyped stmLk ntType termType Unit actions

/-- The verified automaton for `stmGrammar`; `stmTables` contributes only the
(untrusted) automaton half. -/
def automaton : Automaton stmGrammar :=
  Gen.automatonOfG0TablesTyped grammar stmLk ntType termType Unit actions stmTables

/-- Safety — kernel `rfl` (BTree-backed tables; no compiler-trust axiom). -/
theorem stmSafe : Safe automaton := Safe.of_check (by rfl)

/-- Completeness — kernel `rfl` (BTree-backed tables). -/
theorem stmComplete : Complete automaton := Complete.of_check (by rfl)

/-! ### Lexer + end-to-end parsing -/

/-- A token is `Info × Σ t, termType t` with `Info := Unit` here (this demo
doesn't track positions): `NUM` carries its `Nat`, all other terminals carry `()`. -/
abbrev Tok : Type := Unit × ((t : Fin (stmTables.numTerm + 1)) × termType t)

/-- A tiny lexer: digits → `NUM`, and the punctuation tokens; whitespace skipped,
anything else fails. -/
partial def lexAux : List Char → Option (List Tok)
  | [] => some []
  | c :: rest =>
    if c == ' ' || c == '\t' || c == '\n' then lexAux rest
    else if c.isDigit then
      let digs := (c :: rest).takeWhile Char.isDigit
      let n : Nat := digs.foldl (fun acc d => acc * 10 + (d.toNat - 48)) 0
      (lexAux ((c :: rest).dropWhile Char.isDigit)).map ((((), ⟨5, n⟩) : Tok) :: ·)
    else
      let single (i : Fin (stmTables.numTerm + 1)) (_h : termType i = Unit) :=
        (lexAux rest).map ((((), ⟨i, by rw [_h]; exact ()⟩) : Tok) :: ·)
      match c with
      | '+' => single 0 rfl
      | ';' => single 1 rfl
      | '(' => single 2 rfl
      | ')' => single 3 rfl
      | _ => none

/-- Lex a string into a token buffer ending in an infinite `EOF` filler `((), ⟨4, ()⟩)`. -/
def lexString (s : String) : Option (Buffer stmGrammar) :=
  (lexAux s.toList).map (fun toks => Buf.ofListEof toks ((((), ⟨4, ()⟩)) : Tok))

/-- Parse a string into a `Stm` (the start nonterminal's value type). -/
def parseStm (s : String) : Option Stm :=
  match lexString s with
  | none => none
  | some buf =>
    match Main.parse (A := automaton) (0 : Fin 1) stmSafe 50 buf with
    | .Parsed s _ => some s
    | _ => none

/-! ### Acceptance tests

The compiled parser produces a typed `Stm`/`Exp` AST directly. -/

-- A statement wrapping a left-associated sum.
example : parseStm "1+2;" = some (.sExp (.add (.num 1) (.num 2))) := by native_decide
-- Left associativity of `+`.
example : parseStm "1+2+3;" = some (.sExp (.add (.add (.num 1) (.num 2)) (.num 3))) := by
  native_decide
-- Parentheses regroup.
example : parseStm "(1+2)+3;" = some (.sExp (.add (.add (.num 1) (.num 2)) (.num 3))) := by
  native_decide
example : parseStm "1+(2+3);" = some (.sExp (.add (.num 1) (.add (.num 2) (.num 3)))) := by
  native_decide
-- Missing terminating `;` is rejected.
example : parseStm "1+2" = none := by native_decide
-- Dangling operator is rejected.
example : parseStm "1+;" = none := by native_decide

/-! ### Completeness and unambiguity

The heterogeneous automaton supports the full verified stack unchanged. -/

/-- Every parse `tree`, given enough fuel, parses to its own AST, consuming
exactly `word`. -/
theorem stm_parses (logNSteps : Nat) (word : List stmGrammar.Token)
    (bufEnd : Buffer stmGrammar)
    (tree : ParseTree stmGrammar (.NT (automaton.start_nt (0 : Fin 1))) word)
    (hfuel : ptSize tree ≤ 2 ^ logNSteps) :
    Main.parse (A := automaton) (0 : Fin 1) stmSafe logNSteps (word ++ₛ bufEnd)
      = .Parsed (ptSem tree) bufEnd := by
  have H := Main.parse_complete (A := automaton) (0 : Fin 1) stmSafe stmComplete
    logNSteps word bufEnd tree
  cases hp : Main.parse (A := automaton) (0 : Fin 1) stmSafe logNSteps (word ++ₛ bufEnd) with
  | Parsed sem buff => rw [hp] at H; obtain ⟨h1, h2, _⟩ := H; rw [h1, h2]
  | Timeout => rw [hp] at H; omega
  | Fail s t => rw [hp] at H; exact H.elim

/-- **Unambiguity**: any two parse trees of the same word have equal AST. -/
theorem stm_unambiguous (word : List stmGrammar.Token)
    (tree1 tree2 : ParseTree stmGrammar (.NT (automaton.start_nt (0 : Fin 1))) word) :
    ptSem tree1 = ptSem tree2 :=
  Main.unambiguity (A := automaton) (htok := ⟨(((), ⟨4, ()⟩) : Tok)⟩) stmSafe stmComplete
    (0 : Fin 1) word tree1 tree2

end LeanMenhir.Examples.StmCalc
