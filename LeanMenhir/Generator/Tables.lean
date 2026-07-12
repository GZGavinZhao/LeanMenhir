/-
The bridge from *untrusted, index-only* generated tables (`GenTables`) to a
genuine `Automaton` instance (`automatonOfTables`). The dependent proof
obligations carried by `Shift_act` / `goto_table` (`T t = last_symb s`,
`NT nt = last_symb s`) are *reconstructed* at build time via `DecidableEq`
(`if h : … then ⟨_, h⟩ else fail`), so the generator itself need only emit plain
index data; the `isSafe` validator then certifies the whole thing.

Semantic values are kept monomorphic (a single `Val` type for every symbol),
which is exactly what a real AST-producing parser needs and avoids dependent
plumbing in the actions.

LGPL-3.0-or-later (derivative of coq-menhirlib).
-/
import LeanMenhir.Main
import LeanMenhir.Generator.FinAlphabet
import LeanMenhir.Generator.BTree

namespace LeanMenhir
namespace Gen

/-- A grammar/automaton symbol at the (untrusted) generator level: a terminal or
nonterminal index. -/
inductive GSym where
  | term : Nat → GSym
  | nonterm : Nat → GSym
deriving DecidableEq, Repr, Hashable, Inhabited

/-- A lookahead action at the generator level (index data only). -/
inductive GLookahead where
  | shift : Nat → GLookahead        -- target (flat) state index
  | reduce : Nat → GLookahead       -- production index
  | fail : GLookahead
deriving Repr, Inhabited

/-- The action attached to a state (index data only). -/
inductive GAction where
  | defaultReduce : Nat → GAction                 -- production index
  | lookahead : Array GLookahead → GAction        -- indexed by terminal
deriving Repr, Inhabited

/-- The data an LR generator emits. State index `0` is the (single) initial
state; indices `1 … numStates-1` are non-initial states. -/
structure GenTables where
  numTerm : Nat
  numNonterm : Nat
  numProd : Nat
  numStates : Nat
  startNonterm : Nat
  prodLhs : Array Nat                 -- numProd
  prodRhsRev : Array (Array GSym)     -- numProd, reversed RHS
  /-- Jump-table lookup for `prodLhs`, populated by `build_tables%` as a *balanced
  decision tree* over numeric literals. The kernel reduces it in `O(log numProd)`
  per query (via the accelerated `Nat.ble`/`Nat.beq`), versus `O(index)` for
  `Array.getD` (which the kernel reduces by walking the backing `List`). This is
  what lets the heterogeneous `actions` dispatcher — whose dependent return type
  forces one production lookup *per arm* — elaborate in `O(numProd · log numProd)`
  instead of `O(numProd²)` (and without retaining huge intermediate `List`/`Array`
  states, which is the real memory blow-up on large grammars).

  Defaults to the array lookup so hand-written / legacy `GenTables` literals (and
  the `partial` generators `buildTables`/`buildTablesSLR`) keep working unchanged.
  Invariant (enforced by `build_tables%`): `prodLhsFn i = prodLhs.getD i 0` for
  every `i < numProd`. -/
  prodLhsFn : Nat → Nat := fun i => prodLhs.getD i 0
  /-- Jump-table lookup for `prodRhsRev`; see `prodLhsFn`.
  Invariant: `prodRhsRevFn i = prodRhsRev.getD i #[]` for every `i < numProd`. -/
  prodRhsRevFn : Nat → Array GSym := fun i => prodRhsRev.getD i #[]
  incoming : Array (Option GSym)      -- numStates; `none` only for state 0
  action : Array GAction              -- numStates
  /-- `goto[state][nonterm] = some targetState` or `none`. -/
  goto : Array (Array (Option Nat))   -- numStates × numNonterm
  pastSymb : Array (Array GSym)       -- numStates (entry 0 unused)
  pastStateSets : Array (Array (Array Nat)) -- numStates; each a list of state-sets
  nullable : Array Bool               -- numNonterm
  first : Array (Array Nat)           -- numNonterm
  /-- `items[state]` = the LR(1) items of that state, each `(prod, dotPos, lookahead)`
  (one entry per lookahead). Needed only for the completeness validator. -/
  items : Array (Array (Nat × Nat × Nat)) -- numStates
  -- ### Balanced-search-tree views of the state/nonterminal-indexed tables.
  -- `build_tables%` populates these; the kernel-`rfl` bridge's verified accessors
  -- read them via `BTree.find` so a lookup reduces in `O(log n)` with bounded
  -- memory (see `Generator/BTree.lean`). They default to the empty tree, so the
  -- array-backed `automatonOfTables`/`automatonOfTablesTyped` bridges and any
  -- hand-written literals keep working unchanged; every `build_tables%` result
  -- supplies real trees.
  incomingBT : BTree (Option GSym) := .leaf            -- keyed by state
  actionBT : BTree GAction := .leaf                    -- keyed by state
  /-- Flattened `goto`, keyed by `state * (numNonterm + 1) + nonterm`. -/
  gotoBT : BTree (Option Nat) := .leaf
  pastSymbBT : BTree (Array GSym) := .leaf             -- keyed by state
  pastStateSetsBT : BTree (Array (Array Nat)) := .leaf -- keyed by state
  nullableBT : BTree Bool := .leaf                     -- keyed by nonterminal
  firstBT : BTree (Array Nat) := .leaf                 -- keyed by nonterminal
  itemsBT : BTree (Array (Nat × Nat × Nat)) := .leaf   -- keyed by state
-- `Repr` is intentionally *not* derived: `GenTables` now carries function fields
-- (`prodLhsFn`/`prodRhsRevFn`), and functions have no `Repr` instance.
deriving Inhabited

/-- Number of non-initial states. -/
def GenTables.numNonInit (g : GenTables) : Nat := g.numStates - 1

/-- Re-dimension a table blob to a `Grammar0`'s alphabet sizes: all *types* of an
automaton built from the result are `g0`-dimensioned, while the (untrusted)
content stays `t`'s. A dimension mismatch cannot produce ill-typed data — reads
clamp/default and the validators reject. -/
@[reducible] def GenTables.withDims (t : GenTables) (numTerm numNonterm numProd start : Nat) :
    GenTables :=
  { t with numTerm := numTerm, numNonterm := numNonterm,
           numProd := numProd, startNonterm := start }

/-- Clamp a `Nat` into `Fin (n+1)` (totalises index conversion; the extra slot
`n` is a never-referenced dummy). -/
def cl (n i : Nat) : Fin (n + 1) := ⟨min i n, by omega⟩

/-- On in-range indices, the `Fin`-padding conversion `cl` is the identity. -/
theorem cl_val_of_le {n i : Nat} (h : i ≤ n) : (cl n i).val = i := by
  simp only [cl]
  omega

/-- `gsymToSymbol`, generalised to explicit alphabet dimensions (used by the
`Grammar0`-definitional bridges, whose *types* come from the `Grammar0` while
their content may come from untrusted tables). -/
def gsymToSymbolD (nT nNT : Nat) : GSym → Symbol (Fin (nT + 1)) (Fin (nNT + 1))
  | .term i => .T (cl nT i)
  | .nonterm i => .NT (cl nNT i)

/-- Collect the arguments of a (curried) semantic action into a list and apply a
uniform `List Val → Val` action. -/
def collectArrows {Val Sym : Type} (act : List Val → Val) :
    (syms : List Sym) → (acc : List Val) → arrowsRight Val (syms.map (fun _ => Val))
  | [], acc => act acc
  | _ :: rest, acc => fun (v : Val) => collectArrows act rest (acc ++ [v])

variable (g : GenTables)

/-- Convert a generator symbol to a (padded) `Fin`-indexed grammar symbol. -/
def gsymToSymbol : GSym → Symbol (Fin (g.numTerm + 1)) (Fin (g.numNonterm + 1))
  | .term i => .T (cl g.numTerm i)
  | .nonterm i => .NT (cl g.numNonterm i)

/-- The symbol that leads into non-initial state `n` (depends only on `g`). -/
def lastSymbOf (n : Fin (g.numNonInit + 1)) : Symbol (Fin (g.numTerm + 1)) (Fin (g.numNonterm + 1)) :=
  gsymToSymbol g ((g.incoming.getD (n.val + 1) none).getD (.term 0))

/-- Convert a generator lookahead action, reconstructing the `Shift_act` proof
obligation via decidable equality. -/
def gLookToLook (term : Fin (g.numTerm + 1)) (l : GLookahead) :
    LookaheadAction (lastSymbOf g) (Fin (g.numProd + 1)) term :=
  match l with
  | .shift t =>
      let target : Fin (g.numNonInit + 1) := cl g.numNonInit (t - 1)
      if h : (Symbol.T term : Symbol (Fin (g.numTerm + 1)) (Fin (g.numNonterm + 1)))
          = lastSymbOf g target then .Shift_act target h else .Fail_act
  | .reduce p => .Reduce_act (cl g.numProd p)
  | .fail => .Fail_act

/-- Convert a generator action. -/
def gActionToAction (a : GAction) : Action (lastSymbOf g) (Fin (g.numProd + 1)) :=
  match a with
  | .defaultReduce p => .Default_reduce_act (cl g.numProd p)
  | .lookahead arr => .Lookahead_act (fun term => gLookToLook g term (arr.getD term.val .fail))

/-! ### BTree-backed accessors (kernel-`rfl` certificate path).

Identical in *value* to `lastSymbOf`/`gLookToLook`/`gActionToAction`, but the
`incoming` lookup goes through the `incomingBT` jump tree, so the bridges built
on them (`automatonOfTablesBT`) reduce a per-state/per-terminal lookup in
`O(log n)` under the kernel — enabling a kernel-`rfl` certificate on large
automata. The array-backed originals are untouched (so `decide`/`native_decide`
on the array bridges is unaffected). -/

/-- `lastSymbOf` via the `incomingBT` jump tree. -/
def lastSymbOfBT (n : Fin (g.numNonInit + 1)) : Symbol (Fin (g.numTerm + 1)) (Fin (g.numNonterm + 1)) :=
  gsymToSymbol g ((BTree.find none (n.val + 1) g.incomingBT).getD (.term 0))

/-- `gLookToLook` against `lastSymbOfBT`. -/
def gLookToLookBT (term : Fin (g.numTerm + 1)) (l : GLookahead) :
    LookaheadAction (lastSymbOfBT g) (Fin (g.numProd + 1)) term :=
  match l with
  | .shift t =>
      let target : Fin (g.numNonInit + 1) := cl g.numNonInit (t - 1)
      if h : (Symbol.T term : Symbol (Fin (g.numTerm + 1)) (Fin (g.numNonterm + 1)))
          = lastSymbOfBT g target then .Shift_act target h else .Fail_act
  | .reduce p => .Reduce_act (cl g.numProd p)
  | .fail => .Fail_act

/-- `gActionToAction` against `lastSymbOfBT`. -/
def gActionToActionBT (a : GAction) : Action (lastSymbOfBT g) (Fin (g.numProd + 1)) :=
  match a with
  | .defaultReduce p => .Default_reduce_act (cl g.numProd p)
  | .lookahead arr => .Lookahead_act (fun term => gLookToLookBT g term (arr.getD term.val .fail))

/-! ### Goto table + sparse goto enumeration (BTree bridges)

The goto lookup and the *defined-goto enumeration* the safety validators iterate
(`Automaton.goto_enum`). `gotoEnumOfBT` reads only the defined gotos from
`gotoBT.toList` (an `O(defined)` traversal), and `gotoEnumOfBT_complete` proves it
covers every defined goto — the soundness obligation `Automaton.goto_enum_complete`. -/

/-- Flattened goto key for `(s, nt)` (must match the key used to build `gotoBT`). -/
def gotoKeyBT (s : State (Fin 1) (Fin (g.numNonInit + 1))) (nt : Fin (g.numNonterm + 1)) : Nat :=
  (match s with | .Init _ => 0 | .Ninit n => n.val + 1) * (g.numNonterm + 1) + nt.val

/-- The goto table, shared by the typed and monomorphic BTree bridges. -/
def gotoTableOfBT (s : State (Fin 1) (Fin (g.numNonInit + 1))) (nt : Fin (g.numNonterm + 1)) :
    Option { s2 : Fin (g.numNonInit + 1) //
      (Symbol.NT nt : Symbol (Fin (g.numTerm + 1)) (Fin (g.numNonterm + 1))) = lastSymbOfBT g s2 } :=
  match BTree.find none (gotoKeyBT g s nt) g.gotoBT with
  | none => none
  | some t =>
      let target : Fin (g.numNonInit + 1) := cl g.numNonInit (t - 1)
      if h : (Symbol.NT nt : Symbol (Fin (g.numTerm + 1)) (Fin (g.numNonterm + 1)))
          = lastSymbOfBT g target then some ⟨target, h⟩ else none

/-- Decode a flattened goto key back to `(state, nonterminal)` (inverse of
`gotoKeyBT` on in-range inputs; see `decodeGotoBT_gotoKey`). -/
def decodeGotoBT (key : Nat) :
    State (Fin 1) (Fin (g.numNonInit + 1)) × Fin (g.numNonterm + 1) :=
  let sf := key / (g.numNonterm + 1)
  ((if sf = 0 then .Init 0 else .Ninit (cl g.numNonInit (sf - 1))), cl g.numNonterm (key % (g.numNonterm + 1)))

/-- The defined gotos, read sparsely from the BTree (one entry per defined goto). -/
def gotoEnumOfBT : List (State (Fin 1) (Fin (g.numNonInit + 1)) × Fin (g.numNonterm + 1)) :=
  g.gotoBT.toList.map (fun kv => decodeGotoBT g kv.1)

theorem decodeGotoBT_gotoKey (s : State (Fin 1) (Fin (g.numNonInit + 1)))
    (nt : Fin (g.numNonterm + 1)) : decodeGotoBT g (gotoKeyBT g s nt) = (s, nt) := by
  have hW : nt.val < g.numNonterm + 1 := nt.isLt
  have hpos : 0 < g.numNonterm + 1 := Nat.succ_pos _
  have hnt : cl g.numNonterm nt.val = nt := by
    apply Fin.ext; simp only [cl]; exact Nat.min_eq_left (Nat.le_of_lt_succ nt.isLt)
  cases s with
  | Init i =>
    have hi : i = (0 : Fin 1) := Fin.ext (by omega)
    subst hi
    simp only [decodeGotoBT, gotoKeyBT, Nat.zero_mul, Nat.zero_add,
      Nat.div_eq_of_lt hW, Nat.mod_eq_of_lt hW, if_pos, hnt]
  | Ninit n =>
    have hmod : ((n.val + 1) * (g.numNonterm + 1) + nt.val) % (g.numNonterm + 1) = nt.val := by
      rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hW]
    have hdiv : ((n.val + 1) * (g.numNonterm + 1) + nt.val) / (g.numNonterm + 1) = n.val + 1 := by
      rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hW, Nat.zero_add]
    have hs : cl g.numNonInit n.val = n := by
      apply Fin.ext; simp only [cl]; exact Nat.min_eq_left (Nat.le_of_lt_succ n.isLt)
    simp only [decodeGotoBT, gotoKeyBT, hmod, hdiv, Nat.succ_ne_zero, if_false,
      Nat.add_sub_cancel, hs, hnt]

theorem gotoEnumOfBT_complete (s : State (Fin 1) (Fin (g.numNonInit + 1)))
    (nt : Fin (g.numNonterm + 1)) (hne : gotoTableOfBT g s nt ≠ none) :
    (s, nt) ∈ gotoEnumOfBT g := by
  have hfind : BTree.find none (gotoKeyBT g s nt) g.gotoBT ≠ none := by
    intro hf; exact hne (by simp only [gotoTableOfBT, hf])
  have hmem := BTree.find_mem_toList none (gotoKeyBT g s nt) g.gotoBT hfind
  have : decodeGotoBT g (gotoKeyBT g s nt) ∈ gotoEnumOfBT g :=
    List.mem_map.2 ⟨(gotoKeyBT g s nt, _), hmem, rfl⟩
  rwa [decodeGotoBT_gotoKey] at this

/-- Dense enumeration of every `(s, nt)` pair — the trivial `goto_enum` for small /
array bridges (always covers the defined gotos; see `mem_allPairs`). -/
def allPairs {S NT : Type} [Enumerable S] [Enumerable NT] : List (S × NT) :=
  (allList (α := S)).flatMap (fun s => (allList (α := NT)).map (fun nt => (s, nt)))

theorem mem_allPairs {S NT : Type} [Enumerable S] [Enumerable NT] (s : S) (nt : NT) :
    (s, nt) ∈ allPairs (S := S) (NT := NT) :=
  List.mem_flatMap.2 ⟨s, allList_complete s, List.mem_map.2 ⟨nt, allList_complete nt, rfl⟩⟩

variable (Val : Type) (actions : Nat → List Val → Val)

/-- The **grammar half** of the monomorphic array bridge (P1a: still read from
the untrusted tables; the D9 reversal in P1b makes it a definitional function of
`Grammar0`). -/
@[reducible]
def grammarOfTables : Grammar where
  Terminal := Fin (g.numTerm + 1)
  Nonterminal := Fin (g.numNonterm + 1)
  terminalAlphabet := inferInstance
  nonterminalAlphabet := inferInstance
  symbol_semantic_type := fun _ => Val
  Production := Fin (g.numProd + 1)
  productionAlphabet := inferInstance
  -- Real productions use their stored lhs; the *dummy* padding production
  -- `numProd` is mapped to the dummy nonterminal `numNonterm` (which never appears
  -- after a dot and is not the start symbol), so the completeness validators
  -- (`start_future`, `non_terminal_closed`) impose no obligation on it.
  prod_lhs := fun p =>
    if p.val < g.numProd then cl g.numNonterm (g.prodLhs.getD p.val 0)
    else cl g.numNonterm g.numNonterm
  prod_rhs_rev := fun p => (g.prodRhsRev.getD p.val #[]).toList.map (gsymToSymbol g)
  prod_action := fun p =>
    collectArrows (actions p.val) ((g.prodRhsRev.getD p.val #[]).toList.map (gsymToSymbol g)) []
  Token := Fin (g.numTerm + 1) × Val
  token_term := fun t => t.1
  token_sem := fun t => t.2

/-- Build a genuine `Automaton` **for** `grammarOfTables g Val actions` from the
(untrusted) index-only tables `g`. -/
@[reducible]
def automatonOfTables : Automaton (grammarOfTables g Val actions) where
  NonInitState := Fin (g.numNonInit + 1)
  noninitstateAlphabet := inferInstance
  InitState := Fin 1
  initstateAlphabet := inferInstance
  last_symb_of_non_init_state := lastSymbOf g
  start_nt := fun _ => cl g.numNonterm g.startNonterm
  action_table := fun s =>
    let flat := match s with | .Init _ => 0 | .Ninit n => n.val + 1
    gActionToAction g (g.action.getD flat (.lookahead #[]))
  goto_table := fun s nt =>
    let flat := match s with | .Init _ => 0 | .Ninit n => n.val + 1
    match (g.goto.getD flat #[]).getD nt.val none with
    | none => none
    | some t =>
        let target : Fin (g.numNonInit + 1) := cl g.numNonInit (t - 1)
        if h : (Symbol.NT nt : Symbol (Fin (g.numTerm + 1)) (Fin (g.numNonterm + 1)))
            = lastSymbOf g target then some ⟨target, h⟩ else none
  past_symb_of_non_init_state := fun n =>
    (g.pastSymb.getD (n.val + 1) #[]).toList.map (gsymToSymbol g)
  past_state_of_non_init_state := fun n =>
    (g.pastStateSets.getD (n.val + 1) #[]).toList.map (fun (stateSet : Array Nat) =>
      fun (s : State (Fin 1) (Fin (g.numNonInit + 1))) =>
        let flat := match s with | .Init _ => 0 | .Ninit m => m.val + 1
        stateSet.toList.contains flat)
  items_of_state := fun s =>
    let flat := match s with | .Init _ => 0 | .Ninit n => n.val + 1
    (g.items.getD flat #[]).toList.map (fun it =>
      { prod_item := cl g.numProd it.1
        dot_pos_item := it.2.1
        lookaheads_item := [cl g.numTerm it.2.2] })
  -- The dummy nonterminal `numNonterm` is declared nullable so that the dummy
  -- production `numNonterm → ε` satisfies `nullable_stable`; real nonterminals use
  -- the generated table. (The dummy nonterminal never occurs in a real RHS.)
  nullable_nterm := fun nt => if nt.val < g.numNonterm then g.nullable.getD nt.val false else true
  first_nterm := fun nt => (g.first.getD nt.val #[]).toList.map (cl g.numTerm)
  -- dense enumeration (this small/array bridge does not need sparse goto iteration)
  goto_enum := allPairs
  goto_enum_complete := fun s nt _ => mem_allPairs s nt

/-- The **grammar half** of the BTree bridge (jump-table-backed lookups). -/
@[reducible]
def grammarOfTablesBT : Grammar where
  Terminal := Fin (g.numTerm + 1)
  Nonterminal := Fin (g.numNonterm + 1)
  terminalAlphabet := inferInstance
  nonterminalAlphabet := inferInstance
  symbol_semantic_type := fun _ => Val
  Production := Fin (g.numProd + 1)
  productionAlphabet := inferInstance
  prod_lhs := fun p =>
    if p.val < g.numProd then cl g.numNonterm (g.prodLhsFn p.val)
    else cl g.numNonterm g.numNonterm
  prod_rhs_rev := fun p => (g.prodRhsRevFn p.val).toList.map (gsymToSymbol g)
  prod_action := fun p =>
    collectArrows (actions p.val) ((g.prodRhsRevFn p.val).toList.map (gsymToSymbol g)) []
  Token := Fin (g.numTerm + 1) × Val
  token_term := fun t => t.1
  token_sem := fun t => t.2

/-- BTree-backed monomorphic bridge: identical to `automatonOfTables` but every
state/nonterminal-indexed lookup goes through `BTree.find` on the `…BT` fields, so
the `isSafe`/`isComplete` validators reduce in `O(log n)` per lookup under the
kernel — discharge their certificates with `by rfl`. Requires `g` from
`build_tables%` (which populates the trees). -/
@[reducible]
def automatonOfTablesBT : Automaton (grammarOfTablesBT g Val actions) where
  NonInitState := Fin (g.numNonInit + 1)
  noninitstateAlphabet := inferInstance
  InitState := Fin 1
  initstateAlphabet := inferInstance
  last_symb_of_non_init_state := lastSymbOfBT g
  start_nt := fun _ => cl g.numNonterm g.startNonterm
  action_table := fun s =>
    let flat := match s with | .Init _ => 0 | .Ninit n => n.val + 1
    gActionToActionBT g (BTree.find (.lookahead #[]) flat g.actionBT)
  goto_table := gotoTableOfBT g
  past_symb_of_non_init_state := fun n =>
    (BTree.find #[] (n.val + 1) g.pastSymbBT).toList.map (gsymToSymbol g)
  past_state_of_non_init_state := fun n =>
    (BTree.find #[] (n.val + 1) g.pastStateSetsBT).toList.map (fun (stateSet : Array Nat) =>
      fun (s : State (Fin 1) (Fin (g.numNonInit + 1))) =>
        let flat := match s with | .Init _ => 0 | .Ninit m => m.val + 1
        stateSet.toList.contains flat)
  items_of_state := fun s =>
    let flat := match s with | .Init _ => 0 | .Ninit n => n.val + 1
    (BTree.find #[] flat g.itemsBT).toList.map (fun it =>
      { prod_item := cl g.numProd it.1
        dot_pos_item := it.2.1
        lookaheads_item := [cl g.numTerm it.2.2] })
  nullable_nterm := fun nt => if nt.val < g.numNonterm then BTree.find false nt.val g.nullableBT else true
  first_nterm := fun nt => (BTree.find #[] nt.val g.firstBT).toList.map (cl g.numTerm)
  -- sparse goto enumeration: iterate only the defined gotos (gotoBT.toList)
  goto_enum := gotoEnumOfBT g
  goto_enum_complete := gotoEnumOfBT_complete g

/-! ### Heterogeneous (typed) bridge

`automatonOfTables` above keeps semantic values *monomorphic* (one `Val` for every
symbol), which forces an AST-producing front-end (e.g. BNFC) to encode every
category in a tagged union and *project* it back out in each action — and to
fabricate `Inhabited` defaults for the never-reached projection branches.

`automatonOfTablesTyped` instead lets each symbol carry its own type:
`termType t` for terminal `t` and `ntType n` for nonterminal `n`. Actions are
then ordinary typed functions that build the AST directly (no union, no
projection, no `Inhabited`). The verified interpreter and the safety/completeness
validators are generic over `symbol_semantic_type`, so they accept this automaton
unchanged.

The only values ever conjured "from nothing" are `()` at `Unit`: the dummy
padding production (its lhs is the dummy nonterminal, so set `ntType dummyNt :=
Unit`) and the EOF/keyword token payloads (set their `termType := Unit`). No AST
category ever needs a default.

For the dependent dispatcher `actions` to be writable by the caller, the
production data of `g` must *reduce* — i.e. `g` is a concrete `GenTables` literal
(the emitted-tables path, certified by kernel `decide`), not an opaque
`buildTablesSLR` result. -/

/-- The (heterogeneous) semantic-value type of a symbol: `termType` for a
terminal, `ntType` for a nonterminal. -/
def symTypeOf (g : GenTables)
    (ntType : Fin (g.numNonterm + 1) → Type) (termType : Fin (g.numTerm + 1) → Type) :
    Symbol (Fin (g.numTerm + 1)) (Fin (g.numNonterm + 1)) → Type
  | .T t => termType t
  | .NT n => ntType n

/-- The lhs nonterminal of a production (real productions use their stored lhs;
the dummy padding production `numProd` maps to the dummy nonterminal `numNonterm`).
Shared between the `prod_lhs` field and the dependent `actions` parameter type so
the two are definitionally equal. Uses the jump-table `prodLhsFn` so the
dependent `actions` dispatcher elaborates without the `O(index)` array walk. -/
def prodLhsOf (g : GenTables) (p : Fin (g.numProd + 1)) : Fin (g.numNonterm + 1) :=
  if p.val < g.numProd then cl g.numNonterm (g.prodLhsFn p.val)
  else cl g.numNonterm g.numNonterm

/-- The reversed RHS of a production as grammar symbols. Shared between the
`prod_rhs_rev` field and the dependent `actions` parameter type. Uses the
jump-table `prodRhsRevFn`; the dummy production `numProd` yields `[]` (the
`prodRhsRevFn` default returns `#[]` outside `[0, numProd)`). -/
def prodRhsRevOf (g : GenTables) (p : Fin (g.numProd + 1)) :
    List (Symbol (Fin (g.numTerm + 1)) (Fin (g.numNonterm + 1))) :=
  (g.prodRhsRevFn p.val).toList.map (gsymToSymbol g)

/-- Discharge the impossible "out-of-range production index" arm of a dependent
`actions` dispatcher.

The dispatcher `actions : (p : Fin (numProd + 1)) → …` is written as a literal
match `| 0 => … | numProd => …`. Lean's equation compiler only proves a
`Fin n` numeric-literal match *exhaustive* (using the `isLt` bound to rule out
`val ≥ n`) for *small* `n` — beyond ~15 arms it gives up and reports the
out-of-range case `Fin.mk (numProd+1) _` as a "missing case". The fix is to add an
explicit final arm matching every out-of-range index, whose `isLt` proof is then
absurd:

```
def actions : (p : Fin (tables.numProd + 1)) → …
  | 0 => …
  | ⟨numProd⟩ => …                       -- the dummy production
  | ⟨_ + (numProd + 1), h⟩ => elimOutOfRange h
```

`elimOutOfRange` turns the absurd `h : m + K < K` into a value of any type, so the
arm type-checks without the equation compiler needing to reason about the bound. -/
def elimOutOfRange {α : Sort u} {m K : Nat} (h : m + K < K) : α :=
  absurd h (by omega)

/-- The **grammar half** of the typed bridge: heterogeneous semantic values —
terminal `t` carries a `termType t`, nonterminal `n` an `ntType n`; the token is
caller-chosen `Info` (source position, ignored by the parser) plus the dependent
payload `Σ t, termType t`. Each production's `actions p` is its semantic action
in its true curried type. -/
@[reducible]
def grammarOfTablesTyped (g : GenTables)
    (ntType : Fin (g.numNonterm + 1) → Type) (termType : Fin (g.numTerm + 1) → Type)
    (Info : Type)
    (actions : (p : Fin (g.numProd + 1)) →
      arrowsRight (symTypeOf g ntType termType (.NT (prodLhsOf g p)))
                  ((prodRhsRevOf g p).map (symTypeOf g ntType termType))) :
    Grammar where
  Terminal := Fin (g.numTerm + 1)
  Nonterminal := Fin (g.numNonterm + 1)
  terminalAlphabet := inferInstance
  nonterminalAlphabet := inferInstance
  symbol_semantic_type := symTypeOf g ntType termType
  Production := Fin (g.numProd + 1)
  productionAlphabet := inferInstance
  prod_lhs := prodLhsOf g
  prod_rhs_rev := prodRhsRevOf g
  prod_action := actions
  Token := Info × ((t : Fin (g.numTerm + 1)) × termType t)
  token_term := fun x => x.2.1
  token_sem := fun x => x.2.2

/-- Build an `Automaton` **for** `grammarOfTablesTyped …` from the (untrusted)
index-only tables `g` (see the section comment above). -/
@[reducible]
def automatonOfTablesTyped (g : GenTables)
    (ntType : Fin (g.numNonterm + 1) → Type) (termType : Fin (g.numTerm + 1) → Type)
    (Info : Type)
    (actions : (p : Fin (g.numProd + 1)) →
      arrowsRight (symTypeOf g ntType termType (.NT (prodLhsOf g p)))
                  ((prodRhsRevOf g p).map (symTypeOf g ntType termType))) :
    Automaton (grammarOfTablesTyped g ntType termType Info actions) where
  NonInitState := Fin (g.numNonInit + 1)
  noninitstateAlphabet := inferInstance
  InitState := Fin 1
  initstateAlphabet := inferInstance
  last_symb_of_non_init_state := lastSymbOfBT g
  start_nt := fun _ => cl g.numNonterm g.startNonterm
  action_table := fun s =>
    let flat := match s with | .Init _ => 0 | .Ninit n => n.val + 1
    gActionToActionBT g (BTree.find (.lookahead #[]) flat g.actionBT)
  goto_table := gotoTableOfBT g
  past_symb_of_non_init_state := fun n =>
    (BTree.find #[] (n.val + 1) g.pastSymbBT).toList.map (gsymToSymbol g)
  past_state_of_non_init_state := fun n =>
    (BTree.find #[] (n.val + 1) g.pastStateSetsBT).toList.map (fun (stateSet : Array Nat) =>
      fun (s : State (Fin 1) (Fin (g.numNonInit + 1))) =>
        let flat := match s with | .Init _ => 0 | .Ninit m => m.val + 1
        stateSet.toList.contains flat)
  items_of_state := fun s =>
    let flat := match s with | .Init _ => 0 | .Ninit n => n.val + 1
    (BTree.find #[] flat g.itemsBT).toList.map (fun it =>
      { prod_item := cl g.numProd it.1
        dot_pos_item := it.2.1
        lookaheads_item := [cl g.numTerm it.2.2] })
  nullable_nterm := fun nt => if nt.val < g.numNonterm then BTree.find false nt.val g.nullableBT else true
  first_nterm := fun nt => (BTree.find #[] nt.val g.firstBT).toList.map (cl g.numTerm)
  -- sparse goto enumeration: iterate only the defined gotos (gotoBT.toList)
  goto_enum := gotoEnumOfBT g
  goto_enum_complete := gotoEnumOfBT_complete g

end Gen
end LeanMenhir


