/-
The textbook derivation spec on `Grammar0` and the transport theorem (D7′).

`Grammar0.Derives` is a ~15-line, forward-RHS-order, plain-`Nat` inductive
proposition — the definition of "this terminal string is derivable in the
grammar I wrote" that any CFG-literate reader can audit **without touching a
single dependent type**. The transport theorems (`toGrammar_derives_iff`,
`toGrammarTyped_derives_iff`) prove it equivalent to language membership of the
verified grammar (`(g0.toGrammar …).Derives`, i.e. `Nonempty (ParseTree …)`),
so the audit story for every generated parser becomes:

1. read `Grammar0.Derives` (below) and your own `grammar : Grammar0`;
2. believe the transport theorem;
3. read the guarantees in `Guarantees.lean` — their membership hypotheses/
   conclusions are now *literally about your grammar*.

Token payloads never affect derivability (D8): a token word derives iff its
terminal-index string does, which is why the `Grammar0`-level language is over
`List Nat`.

LGPL-3.0-or-later (derivative of coq-menhirlib).
-/
import LeanMenhir.Generator.Grammar0
import LeanMenhir.Spec.Language

namespace LeanMenhir
namespace Gen
namespace Grammar0

/-! ### Well-formedness -/

/-- Well-formedness of a `Grammar0` (Prop form of the decidable `wf`): the start
symbol and every index in every production lie within the declared alphabets.
Under `WF`, the `Fin` padding in the derived grammar never clamps and the dummy
symbols are unreachable. -/
structure WF (g0 : Grammar0) : Prop where
  start_lt : g0.start < g0.numNonterm
  lhs_lt : ∀ p ∈ g0.prods.toList, p.1 < g0.numNonterm
  rhs_lt : ∀ p ∈ g0.prods.toList, ∀ s ∈ p.2.toList,
    match s with
    | .term t => t < g0.numTerm
    | .nonterm n => n < g0.numNonterm

/-- Certified constructor: discharge `g0.WF` by `WF.of_check (by decide)`. -/
theorem WF.of_check {g0 : Grammar0} (h : g0.wf = true) : g0.WF := by
  unfold wf at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hstart, hp⟩ := h
  refine ⟨of_decide_eq_true hstart, fun p hp' => ?_, fun p hp' s hs => ?_⟩ <;>
    (have h12 := hp p hp'; rw [Bool.and_eq_true] at h12)
  · exact of_decide_eq_true h12.1
  · have h2 := h12.2
    rw [List.all_eq_true] at h2
    have h3 := h2 s hs
    cases s with
    | term t => exact of_decide_eq_true h3
    | nonterm n => exact of_decide_eq_true h3

/-- **Reflection**: `wf` decides exactly `WF`. -/
theorem WF.check_iff {g0 : Grammar0} : g0.wf = true ↔ g0.WF := by
  refine ⟨WF.of_check, fun h => ?_⟩
  unfold wf
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨decide_eq_true h.start_lt, fun p hp => ?_⟩
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨decide_eq_true (h.lhs_lt p hp), fun s hs => ?_⟩
  have h3 := h.rhs_lt p hp s hs
  cases s with
  | term t => exact decide_eq_true h3
  | nonterm n => exact decide_eq_true h3

/-- `g0.WF` is decidable — `by decide` runs the boolean `wf`. -/
instance {g0 : Grammar0} : Decidable g0.WF := decidable_of_iff _ WF.check_iff

/-! ### The textbook derivation relation -/

mutual
/-- **Textbook CFG derivation over the grammar exactly as you wrote it**:
`g0.Derives s w` says the terminal-index string `w` derives from symbol `s` —
a terminal derives itself, and a nonterminal derives the concatenation of
strings derived by the right-hand side (in forward order) of one of its
productions. Plain numbers, no dependent types, no reversed lists. -/
inductive Derives (g0 : Grammar0) : GSym → List Nat → Prop
  | leaf (t : Nat) : Derives g0 (.term t) [t]
  | node (i : Nat) (hi : i < g0.prods.size) (ws : List (List Nat)) :
      DerivesAll g0 (g0.prods[i]).2.toList ws →
      Derives g0 (.nonterm (g0.prods[i]).1) ws.flatten

/-- Each symbol of a list derives the corresponding string. -/
inductive DerivesAll (g0 : Grammar0) : List GSym → List (List Nat) → Prop
  | nil : DerivesAll g0 [] []
  | cons {s : GSym} {ss : List GSym} {w : List Nat} {ws : List (List Nat)} :
      Derives g0 s w → DerivesAll g0 ss ws → DerivesAll g0 (s :: ss) (w :: ws)
end

/-! ### Bridge infrastructure

`toGrammar` and `toGrammarTyped` differ only in their token/semantic fields;
`bridgeG` abstracts exactly that difference, so the transport argument below is
proved once and instantiated twice. Everything in this section is private
scaffolding for the two transport theorems. -/

/-- Erase a `Fin`-padded grammar symbol back to a numeric `GSym`. -/
private def symErase {nT nNT : Nat} : Symbol (Fin (nT + 1)) (Fin (nNT + 1)) → GSym
  | .T t => .term t.val
  | .NT n => .nonterm n.val

/-- A symbol of the derived grammar the erasure can recurse through: any
terminal, or a *real* nonterminal (below the dummy index `numNonterm`). -/
private def GoodSym (g0 : Grammar0) :
    Symbol (Fin (g0.numTerm + 1)) (Fin (g0.numNonterm + 1)) → Prop
  | .T _ => True
  | .NT fn => fn.val < g0.numNonterm

private theorem getD_eq_getElem {α : Type} (a : Array α) (d : α) {i : Nat}
    (hi : i < a.size) : a.getD i d = a[i] := by
  simp [Array.getD, hi]

/-- Erasure inverts the `Fin` padding on an in-range `GSym` list. -/
private theorem list_map_erase (nT nNT : Nat) :
    ∀ l : List GSym,
      (∀ s ∈ l, match s with | .term t => t < nT | .nonterm n => n < nNT) →
      (l.map (gsymToSymbolD nT nNT)).map symErase = l
  | [], _ => rfl
  | s :: rest, h => by
    rw [List.map_cons, List.map_cons,
      list_map_erase nT nNT rest (fun s hs => h s (List.mem_cons_of_mem _ hs))]
    have hs := h s List.mem_cons_self
    cases s with
    | term t =>
      show GSym.term (cl nT t).val :: rest = GSym.term t :: rest
      rw [cl_val_of_le (Nat.le_of_lt hs)]
    | nonterm n =>
      show GSym.nonterm (cl nNT n).val :: rest = GSym.nonterm n :: rest
      rw [cl_val_of_le (Nat.le_of_lt hs)]

/-- `DerivesAll` is closed under appending one more derivation. -/
private theorem DerivesAll.snoc {g0 : Grammar0} :
    {l : List GSym} → {ws : List (List Nat)} → DerivesAll g0 l ws →
    {s : GSym} → {w : List Nat} → Derives g0 s w →
    DerivesAll g0 (l ++ [s]) (ws ++ [w])
  | _, _, .nil, _, _, h => .cons h .nil
  | _, _, .cons hd tl, _, _, h => .cons hd (DerivesAll.snoc tl h)

/-- Extend a `ParseTreeList` at the far end of the (reversed) symbol list — the
*first* symbol in grammar order, so its word chunk goes in front. -/
private theorem ptl_snoc {G : Grammar} :
    {ss : List (Symbol G.Terminal G.Nonterminal)} → {w : List G.Token} →
    ParseTreeList G ss w →
    {s : Symbol G.Terminal G.Nonterminal} → {wt : List G.Token} → ParseTree G s wt →
    Nonempty (ParseTreeList G (ss ++ [s]) (wt ++ w))
  | _, _, .nil, _, wt, t => by
    rw [List.append_nil]
    exact ⟨.cons .nil t⟩
  | _, _, .cons q t', _, _, t => by
    obtain ⟨q'⟩ := ptl_snoc q t
    rw [← List.append_assoc]
    exact ⟨.cons q' t'⟩

/-- The common shape of `toGrammar`/`toGrammarTyped`: production fields are the
`Grammar0`-definitional `prodLhs0`/`prodRhsRev0`; token and semantic fields are
parameters. Reducible so that both bridges unify with it definitionally. -/
@[reducible] private def bridgeG (g0 : Grammar0) (lk : ProdLookup g0)
    (SemT : Symbol (Fin (g0.numTerm + 1)) (Fin (g0.numNonterm + 1)) → Type)
    (Tok : Type) (tterm : Tok → Fin (g0.numTerm + 1))
    (tsem : (tok : Tok) → SemT (.T (tterm tok)))
    (pact : (p : Fin (g0.prods.size + 1)) →
      arrowsRight (SemT (.NT (prodLhs0 g0 lk p))) ((prodRhsRev0 g0 lk p).map SemT)) :
    Grammar where
  Terminal := Fin (g0.numTerm + 1)
  Nonterminal := Fin (g0.numNonterm + 1)
  terminalAlphabet := inferInstance
  nonterminalAlphabet := inferInstance
  symbol_semantic_type := SemT
  Production := Fin (g0.prods.size + 1)
  productionAlphabet := inferInstance
  prod_lhs := prodLhs0 g0 lk
  prod_rhs_rev := prodRhsRev0 g0 lk
  prod_action := pact
  Token := Tok
  token_term := tterm
  token_sem := tsem

mutual
/-- Erase a parse tree over a good symbol to a textbook derivation of the
erased terminal-index word. The dummy padding production is impossible: its lhs
is the dummy nonterminal, contradicting `GoodSym`. -/
private theorem pt_erase (g0 : Grammar0) (hwf : g0.WF) (lk : ProdLookup g0)
    (SemT : Symbol (Fin (g0.numTerm + 1)) (Fin (g0.numNonterm + 1)) → Type)
    (Tok : Type) (tterm : Tok → Fin (g0.numTerm + 1))
    (tsem : (tok : Tok) → SemT (.T (tterm tok)))
    (pact : (p : Fin (g0.prods.size + 1)) →
      arrowsRight (SemT (.NT (prodLhs0 g0 lk p))) ((prodRhsRev0 g0 lk p).map SemT)) :
    {s : Symbol (Fin (g0.numTerm + 1)) (Fin (g0.numNonterm + 1))} → {w : List Tok} →
    ParseTree (bridgeG g0 lk SemT Tok tterm tsem pact) s w → GoodSym g0 s →
    g0.Derives (symErase s) (w.map fun tok => (tterm tok).val)
  | _, _, .leaf tok, _ => .leaf _
  | _, w, .node prod ptl, hgood => by
    have hgood' : (prodLhs0 g0 lk prod).val < g0.numNonterm := hgood
    by_cases hp : prod.val < g0.prods.size
    · have hgetD : g0.prods.getD prod.val (0, #[]) = g0.prods[prod.val] :=
        getD_eq_getElem _ _ hp
      have hmem : g0.prods[prod.val] ∈ g0.prods.toList := Array.getElem_mem_toList hp
      have hgoodss : ∀ s ∈ prodRhsRev0 g0 lk prod, GoodSym g0 s := by
        intro s hs
        rw [prodRhsRev0_eq g0 lk prod hp, hgetD] at hs
        obtain ⟨gs, hgs, rfl⟩ := List.mem_map.1 hs
        have hr := hwf.rhs_lt _ hmem gs (List.mem_reverse.1 hgs)
        cases gs with
        | term t => exact True.intro
        | nonterm n =>
          show (cl g0.numNonterm n).val < g0.numNonterm
          rw [cl_val_of_le (Nat.le_of_lt hr)]
          exact hr
      obtain ⟨ws, hall, hw⟩ := ptl_erase g0 hwf lk SemT Tok tterm tsem pact ptl hgoodss
      have hall' : DerivesAll g0 (((prodRhsRev0 g0 lk prod).map symErase).reverse) ws := hall
      have hcond : ∀ s ∈ (g0.prods[prod.val]).2.toList.reverse,
          match s with | .term t => t < g0.numTerm | .nonterm n => n < g0.numNonterm :=
        fun s hs => hwf.rhs_lt _ hmem s (List.mem_reverse.1 hs)
      rw [prodRhsRev0_eq g0 lk prod hp, hgetD, list_map_erase _ _ _ hcond,
        List.reverse_reverse] at hall'
      have hlt' : (g0.prods.getD prod.val (0, #[])).1 ≤ g0.numNonterm := by
        rw [hgetD]
        exact Nat.le_of_lt (hwf.lhs_lt _ hmem)
      have hlv : (prodLhs0 g0 lk prod).val = (g0.prods[prod.val]).1 := by
        rw [prodLhs0_val g0 lk prod hp hlt', hgetD]
      show g0.Derives (.nonterm (prodLhs0 g0 lk prod).val) (w.map fun tok => (tterm tok).val)
      rw [hlv, hw]
      exact .node prod.val hp ws hall'
    · exfalso
      unfold prodLhs0 at hgood'
      rw [if_neg hp, cl_val_of_le (Nat.le_refl _)] at hgood'
      exact absurd hgood' (Nat.lt_irrefl _)

/-- List version of `pt_erase`: erase to a `DerivesAll` over the *forward* RHS
(as the reverse of the tree's reversed symbol list). -/
private theorem ptl_erase (g0 : Grammar0) (hwf : g0.WF) (lk : ProdLookup g0)
    (SemT : Symbol (Fin (g0.numTerm + 1)) (Fin (g0.numNonterm + 1)) → Type)
    (Tok : Type) (tterm : Tok → Fin (g0.numTerm + 1))
    (tsem : (tok : Tok) → SemT (.T (tterm tok)))
    (pact : (p : Fin (g0.prods.size + 1)) →
      arrowsRight (SemT (.NT (prodLhs0 g0 lk p))) ((prodRhsRev0 g0 lk p).map SemT)) :
    {ss : List (Symbol (Fin (g0.numTerm + 1)) (Fin (g0.numNonterm + 1)))} → {w : List Tok} →
    ParseTreeList (bridgeG g0 lk SemT Tok tterm tsem pact) ss w →
    (∀ s ∈ ss, GoodSym g0 s) →
    ∃ ws, DerivesAll g0 ((ss.map symErase).reverse) ws ∧
      w.map (fun tok => (tterm tok).val) = ws.flatten
  | _, _, .nil, _ => ⟨[], .nil, rfl⟩
  | _, _, @ParseTreeList.cons _ _ _ q _ wt t, hss => by
    obtain ⟨ws, hall, hw⟩ := ptl_erase g0 hwf lk SemT Tok tterm tsem pact q
      (fun s hs => hss s (List.mem_cons_of_mem _ hs))
    have ht := pt_erase g0 hwf lk SemT Tok tterm tsem pact t (hss _ List.mem_cons_self)
    refine ⟨ws ++ [wt.map (fun tok => (tterm tok).val)], ?_, ?_⟩
    · rw [List.map_cons, List.reverse_cons]
      exact hall.snoc ht
    · rw [List.map_append, hw, List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil]
end

mutual
/-- Rebuild a parse tree from a textbook derivation, for *any* token word whose
terminal-index string matches (payloads are irrelevant to derivability). -/
private theorem derives_to_pt (g0 : Grammar0) (hwf : g0.WF) (lk : ProdLookup g0)
    (SemT : Symbol (Fin (g0.numTerm + 1)) (Fin (g0.numNonterm + 1)) → Type)
    (Tok : Type) (tterm : Tok → Fin (g0.numTerm + 1))
    (tsem : (tok : Tok) → SemT (.T (tterm tok)))
    (pact : (p : Fin (g0.prods.size + 1)) →
      arrowsRight (SemT (.NT (prodLhs0 g0 lk p))) ((prodRhsRev0 g0 lk p).map SemT)) :
    {s0 : GSym} → {w0 : List Nat} → Derives g0 s0 w0 →
    ∀ word : List Tok, word.map (fun tok => (tterm tok).val) = w0 →
    Nonempty (ParseTree (bridgeG g0 lk SemT Tok tterm tsem pact)
      (gsymToSymbolD g0.numTerm g0.numNonterm s0) word)
  | _, _, .leaf t => by
    intro word hword
    cases word with
    | nil => simp at hword
    | cons tok rest =>
      rw [List.map_cons] at hword
      injection hword with h1 h2
      obtain rfl : rest = [] := List.map_eq_nil_iff.1 h2
      subst h1
      simp only [gsymToSymbolD]
      rw [show cl g0.numTerm (tterm tok).val = tterm tok from
        Fin.ext (cl_val_of_le (Nat.le_of_lt_succ (tterm tok).isLt))]
      exact ⟨ParseTree.leaf (G := bridgeG g0 lk SemT Tok tterm tsem pact) tok⟩
  | _, _, .node i hi ws hall => by
    intro word hword
    have hii : i < g0.prods.size + 1 := Nat.lt_succ_of_lt hi
    have hgetD : g0.prods.getD i (0, #[]) = g0.prods[i] := getD_eq_getElem _ _ hi
    have hmem : g0.prods[i] ∈ g0.prods.toList := Array.getElem_mem_toList hi
    have hlhs_le : (g0.prods[i]).1 ≤ g0.numNonterm := Nat.le_of_lt (hwf.lhs_lt _ hmem)
    obtain ⟨ptl⟩ := derivesAll_to_ptl g0 hwf lk SemT Tok tterm tsem pact hall word hword
    have hrhs : prodRhsRev0 g0 lk ⟨i, hii⟩ =
        ((g0.prods[i]).2.toList.reverse).map (gsymToSymbolD g0.numTerm g0.numNonterm) := by
      rw [prodRhsRev0_eq g0 lk ⟨i, hii⟩ hi, hgetD]
    have hptl : Nonempty (ParseTreeList (bridgeG g0 lk SemT Tok tterm tsem pact)
        (prodRhsRev0 g0 lk ⟨i, hii⟩) word) := by
      rw [hrhs]
      exact ⟨ptl⟩
    obtain ⟨ptl'⟩ := hptl
    have hlt' : (g0.prods.getD i (0, #[])).1 ≤ g0.numNonterm := by
      rw [hgetD]
      exact hlhs_le
    have hlhs : prodLhs0 g0 lk ⟨i, hii⟩ = cl g0.numNonterm (g0.prods[i]).1 := by
      apply Fin.ext
      rw [prodLhs0_val g0 lk ⟨i, hii⟩ hi hlt', hgetD, cl_val_of_le hlhs_le]
    simp only [gsymToSymbolD]
    rw [← hlhs]
    exact ⟨ParseTree.node (G := bridgeG g0 lk SemT Tok tterm tsem pact) ⟨i, hii⟩ ptl'⟩

/-- List version of `derives_to_pt`: rebuild the `ParseTreeList` over the
reversed RHS, splitting the token word along the derived chunks. -/
private theorem derivesAll_to_ptl (g0 : Grammar0) (hwf : g0.WF) (lk : ProdLookup g0)
    (SemT : Symbol (Fin (g0.numTerm + 1)) (Fin (g0.numNonterm + 1)) → Type)
    (Tok : Type) (tterm : Tok → Fin (g0.numTerm + 1))
    (tsem : (tok : Tok) → SemT (.T (tterm tok)))
    (pact : (p : Fin (g0.prods.size + 1)) →
      arrowsRight (SemT (.NT (prodLhs0 g0 lk p))) ((prodRhsRev0 g0 lk p).map SemT)) :
    {l : List GSym} → {ws0 : List (List Nat)} → DerivesAll g0 l ws0 →
    ∀ word : List Tok, word.map (fun tok => (tterm tok).val) = ws0.flatten →
    Nonempty (ParseTreeList (bridgeG g0 lk SemT Tok tterm tsem pact)
      (l.reverse.map (gsymToSymbolD g0.numTerm g0.numNonterm)) word)
  | _, _, .nil => by
    intro word hword
    rw [List.flatten_nil] at hword
    obtain rfl : word = [] := List.map_eq_nil_iff.1 hword
    exact ⟨.nil⟩
  | _, _, .cons hd tl => by
    intro word hword
    rw [List.flatten_cons] at hword
    obtain ⟨w1, w2, rfl, h1, h2⟩ := List.map_eq_append_iff.1 hword
    obtain ⟨t⟩ := derives_to_pt g0 hwf lk SemT Tok tterm tsem pact hd w1 h1
    obtain ⟨q⟩ := derivesAll_to_ptl g0 hwf lk SemT Tok tterm tsem pact tl w2 h2
    rw [List.reverse_cons, List.map_append]
    exact ptl_snoc q t
end

/-- The transport theorem, proved once for the common bridge shape. -/
private theorem bridge_derives_iff (g0 : Grammar0) (hwf : g0.WF) (lk : ProdLookup g0)
    (SemT : Symbol (Fin (g0.numTerm + 1)) (Fin (g0.numNonterm + 1)) → Type)
    (Tok : Type) (tterm : Tok → Fin (g0.numTerm + 1))
    (tsem : (tok : Tok) → SemT (.T (tterm tok)))
    (pact : (p : Fin (g0.prods.size + 1)) →
      arrowsRight (SemT (.NT (prodLhs0 g0 lk p))) ((prodRhsRev0 g0 lk p).map SemT))
    {nt : Nat} (hnt : nt < g0.numNonterm) (word : List Tok) :
    (bridgeG g0 lk SemT Tok tterm tsem pact).Derives (cl g0.numNonterm nt) word ↔
      g0.Derives (.nonterm nt) (word.map fun tok => (tterm tok).val) := by
  have hval : (cl g0.numNonterm nt).val = nt := cl_val_of_le (Nat.le_of_lt hnt)
  constructor
  · rintro ⟨pt⟩
    have h := pt_erase g0 hwf lk SemT Tok tterm tsem pact pt
      (show (cl g0.numNonterm nt).val < g0.numNonterm by rw [hval]; exact hnt)
    have h' : g0.Derives (.nonterm (cl g0.numNonterm nt).val)
        (word.map fun tok => (tterm tok).val) := h
    rwa [hval] at h'
  · intro h
    exact derives_to_pt g0 hwf lk SemT Tok tterm tsem pact h word rfl

/-! ### Transport: the verified grammar's language *is* `Grammar0.Derives`

The verified grammar's membership (`Grammar.Derives`, i.e. the existence of a
`ParseTree`) coincides with the textbook relation on the terminal-index string.
Token payloads are irrelevant to derivability (they only determine the semantic
value), which the `∀ word` quantification over token words makes precise. -/

/-- Transport for the **monomorphic** bridge: a token word is in the language of
`nt` in the derived grammar iff its terminal-index string is `Derives`-derivable
from `nt` in the `Grammar0` itself. -/
theorem toGrammar_derives_iff (g0 : Grammar0) (hwf : g0.WF) (lk : ProdLookup g0)
    (Val : Type) (actions : Nat → List Val → Val)
    {nt : Nat} (hnt : nt < g0.numNonterm)
    (word : List ((g0.toGrammar lk Val actions).Token)) :
    (g0.toGrammar lk Val actions).Derives (cl g0.numNonterm nt) word ↔
      g0.Derives (.nonterm nt) (word.map (fun tok => tok.1.val)) :=
  bridge_derives_iff g0 hwf lk (fun _ => Val) (Fin (g0.numTerm + 1) × Val)
    (fun t => t.1) (fun t => t.2)
    (fun p => collectArrows (actions p.val) (prodRhsRev0 g0 lk p) []) hnt word

/-- Transport for the **typed** bridge. -/
theorem toGrammarTyped_derives_iff (g0 : Grammar0) (hwf : g0.WF) (lk : ProdLookup g0)
    (ntType : Fin (g0.numNonterm + 1) → Type) (termType : Fin (g0.numTerm + 1) → Type)
    (Info : Type)
    (actions : (p : Fin (g0.prods.size + 1)) →
      arrowsRight (symType0 g0 ntType termType (.NT (prodLhs0 g0 lk p)))
                  ((prodRhsRev0 g0 lk p).map (symType0 g0 ntType termType)))
    {nt : Nat} (hnt : nt < g0.numNonterm)
    (word : List ((g0.toGrammarTyped lk ntType termType Info actions).Token)) :
    (g0.toGrammarTyped lk ntType termType Info actions).Derives (cl g0.numNonterm nt) word ↔
      g0.Derives (.nonterm nt) (word.map (fun tok => tok.2.1.val)) :=
  bridge_derives_iff g0 hwf lk (symType0 g0 ntType termType)
    (Info × ((t : Fin (g0.numTerm + 1)) × termType t))
    (fun x => x.2.1) (fun x => x.2.2) actions hnt word

end Grammar0
end Gen
end LeanMenhir
