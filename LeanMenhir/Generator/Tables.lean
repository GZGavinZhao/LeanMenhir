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
  incoming : Array (Option GSym)      -- numStates; `none` only for state 0
  action : Array GAction              -- numStates
  /-- `goto[state][nonterm] = some targetState` or `none`. -/
  goto : Array (Array (Option Nat))   -- numStates × numNonterm
  pastSymb : Array (Array GSym)       -- numStates (entry 0 unused)
  pastStateSets : Array (Array (Array Nat)) -- numStates; each a list of state-sets
  nullable : Array Bool               -- numNonterm
  first : Array (Array Nat)           -- numNonterm
deriving Inhabited

/-- Number of non-initial states. -/
def GenTables.numNonInit (g : GenTables) : Nat := g.numStates - 1

/-- Clamp a `Nat` into `Fin (n+1)` (totalises index conversion; the extra slot
`n` is a never-referenced dummy). -/
def cl (n i : Nat) : Fin (n + 1) := ⟨min i n, by omega⟩

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

variable (Val : Type) (actions : Nat → List Val → Val)

/-- Build a genuine `Automaton` from the (untrusted) index-only tables `g`, with
monomorphic semantic values `Val` and per-production actions `actions`. -/
@[reducible]
def automatonOfTables : Automaton where
  Terminal := Fin (g.numTerm + 1)
  Nonterminal := Fin (g.numNonterm + 1)
  terminalAlphabet := inferInstance
  nonterminalAlphabet := inferInstance
  symbol_semantic_type := fun _ => Val
  Production := Fin (g.numProd + 1)
  productionAlphabet := inferInstance
  prod_lhs := fun p => cl g.numNonterm (g.prodLhs.getD p.val 0)
  prod_rhs_rev := fun p => (g.prodRhsRev.getD p.val #[]).toList.map (gsymToSymbol g)
  prod_action := fun p =>
    collectArrows (actions p.val) ((g.prodRhsRev.getD p.val #[]).toList.map (gsymToSymbol g)) []
  Token := Fin (g.numTerm + 1) × Val
  token_term := fun t => t.1
  token_sem := fun t => t.2
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
        stateSet.contains flat)
  items_of_state := fun _ => []
  nullable_nterm := fun nt => g.nullable.getD nt.val false
  first_nterm := fun nt => (g.first.getD nt.val #[]).toList.map (cl g.numTerm)

end Gen
end LeanMenhir


