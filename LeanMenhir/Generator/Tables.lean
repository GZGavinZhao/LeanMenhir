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

/- Note: the *grammar* half of a verified `Grammar` is never reconstructed from
the untrusted tables — it is always a definitional function of the reviewed
`Grammar0` (see `Generator/Grammar0.lean`). This file supplies only the
untrusted *automaton* half and the shared decoding helpers. -/

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

end Gen
end LeanMenhir


