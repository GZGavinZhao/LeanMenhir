/-
An (untrusted) canonical LR(1) automaton generator. Produces `GenTables` from a
grammar description; the `isSafe` validator certifies the result, so this code
need not be proved correct.

LGPL-3.0-or-later (derivative of coq-menhirlib).
-/
import LeanMenhir.Generator.Tables

namespace LeanMenhir
namespace Gen

/-- A grammar description for the generator. Terminals `0..numTerm-1`,
nonterminals `0..numNonterm-1`. `start` must have exactly the productions whose
RHS ends in `eof`. -/
structure Grammar0 where
  numTerm : Nat
  numNonterm : Nat
  /-- Each production: `(lhs, rhs)` with `rhs` in forward order. -/
  prods : Array (Nat × Array GSym)
  start : Nat
  eof : Nat
deriving Inhabited

namespace Grammar0
variable (g : Grammar0)

def numProd : Nat := g.prods.size
def lhsOf (p : Nat) : Nat := (g.prods.getD p (0, #[])).1
def rhsOf (p : Nat) : Array GSym := (g.prods.getD p (0, #[])).2

/-! ### nullable / first -/

/-- A symbol list is nullable given a `nullable` table for nonterminals. -/
def seqNullable (nl : Array Bool) (rhs : Array GSym) : Bool :=
  rhs.all (fun s => match s with | .term _ => false | .nonterm i => nl.getD i false)

partial def computeNullable : Array Bool := Id.run do
  let mut cur : Array Bool := Array.replicate g.numNonterm false
  let mut changed := true
  while changed do
    changed := false
    for p in g.prods do
      let (lhs, rhs) := p
      if !(cur.getD lhs false) && seqNullable cur rhs then
        cur := cur.set! lhs true
        changed := true
  return cur

/-- Insert `x` into a sorted-dedup `List Nat` (here just dedup). -/
def insertN (x : Nat) (l : List Nat) : List Nat := if l.contains x then l else x :: l
def unionN (a b : List Nat) : List Nat := a.foldl (fun acc x => insertN x acc) b

partial def computeFirst (nl : Array Bool) : Array (List Nat) := Id.run do
  let mut cur : Array (List Nat) := Array.replicate g.numNonterm []
  let mut changed := true
  while changed do
    changed := false
    for p in g.prods do
      let (lhs, rhs) := p
      -- first of the rhs accumulated into lhs
      let mut i := 0
      let mut stop := false
      while i < rhs.size && !stop do
        match rhs.getD i (.term 0) with
        | .term t =>
            let old := cur.getD lhs []
            let new := insertN t old
            if new.length != old.length then cur := cur.set! lhs new; changed := true
            stop := true
        | .nonterm j =>
            let old := cur.getD lhs []
            let new := unionN (cur.getD j []) old
            if new.length != old.length then cur := cur.set! lhs new; changed := true
            if !(nl.getD j false) then stop := true
        i := i + 1
  return cur

/-- FIRST of a symbol sequence followed by lookahead terminal `la`. -/
def firstOfSeq (nl : Array Bool) (fst : Array (List Nat)) :
    List GSym → Nat → List Nat
  | [], la => [la]
  | .term t :: _, _ => [t]
  | .nonterm j :: rest, la =>
      if nl.getD j false then unionN (fst.getD j []) (firstOfSeq nl fst rest la)
      else fst.getD j []

end Grammar0

/-! ### LR(1) items and states -/

/-- An LR(1) item: production, dot position, lookahead terminal. -/
structure Item where
  prod : Nat
  dot : Nat
  la : Nat
deriving DecidableEq, Repr, Hashable, Ord, Inhabited

/-- Normalise an item set: dedup. -/
def normItems (l : List Item) : List Item :=
  l.foldl (fun acc x => if acc.contains x then acc else x :: acc) []

def itemsEq (a b : List Item) : Bool :=
  a.all (fun x => b.contains x) && b.all (fun x => a.contains x)

namespace Grammar0
variable (g : Grammar0) (nl : Array Bool) (fst : Array (List Nat))

/-- The symbol just after the dot, if any. -/
def afterDot (it : Item) : Option GSym := (g.rhsOf it.prod)[it.dot]?

/-- LR(1) closure of an item set. -/
partial def closure (items : List Item) : List Item := Id.run do
  let mut work := items
  let mut acc : List Item := normItems items
  while !work.isEmpty do
    let it := work.head!
    work := work.tail!
    match afterDot g it with
    | some (.nonterm b) =>
        let rest := ((g.rhsOf it.prod).toList.drop (it.dot + 1))
        let las := firstOfSeq nl fst rest it.la
        for p in [0:g.numProd] do
          if g.lhsOf p == b then
            for la in las do
              let ni : Item := ⟨p, 0, la⟩
              if !(acc.contains ni) then
                acc := ni :: acc
                work := ni :: work
    | _ => pure ()
  return acc

/-- `goto` of an item set on a symbol. -/
def goto (items : List Item) (x : GSym) : List Item :=
  let moved := items.filterMap (fun it =>
    match afterDot g it with
    | some y => if y == x then some (⟨it.prod, it.dot + 1, it.la⟩ : Item) else none
    | none => none)
  closure g nl fst moved

/-- All symbols appearing immediately after a dot in an item set. -/
def nextSymbols (items : List Item) : List GSym :=
  items.foldl (fun acc it => match afterDot g it with
    | some x => if acc.contains x then acc else x :: acc
    | none => acc) []

end Grammar0

/-! ### State collection and table assembly -/

/-- Longest common prefix of two `GSym` lists. -/
def commonPrefixSym : List GSym → List GSym → List GSym
  | x :: xs, y :: ys => if x == y then x :: commonPrefixSym xs ys else []
  | _, _ => []

/-- Longest common prefix of a nonempty list of `GSym` lists. -/
def commonPrefixSymAll : List (List GSym) → List GSym
  | [] => []
  | [x] => x
  | x :: xs => commonPrefixSym x (commonPrefixSymAll xs)

/-- Position-wise union of two state-set lists (truncates to the shorter). -/
def mergeStateSets : List (List Nat) → List (List Nat) → List (List Nat)
  | x :: xs, y :: ys => Grammar0.unionN x y :: mergeStateSets xs ys
  | _, _ => []

def mergeStateSetsAll : List (List (List Nat)) → List (List (List Nat)) → List (List (List Nat))
  | _, _ => []  -- unused placeholder

namespace Grammar0
variable (g : Grammar0)

/-- The canonical LR(1) automaton's `GenTables`. -/
partial def buildTables : GenTables := Id.run do
  let nl := g.computeNullable
  let fst := g.computeFirst nl
  -- initial item set: closure of [S → • α, t] for all start productions and all
  -- lookaheads `t`. coq-menhirlib's `start_future` requires the start items to
  -- carry every terminal as lookahead; these extra lookaheads only propagate
  -- along the (non-nullable, eof-terminated) start spine, so the rest of the
  -- canonical LR(1) automaton is unchanged. We range over `[0 : numTerm + 1]`
  -- (not just the real terminals) because the `Automaton`'s terminal type is the
  -- padded `Fin (numTerm + 1)`, and `start_future`/`Allb` quantify over its dummy
  -- element too.
  let initItems : List Item := Id.run do
    let mut acc : List Item := []
    for p in [0:g.numProd] do
      if g.lhsOf p == g.start then
        for t in [0:g.numTerm + 1] do
          acc := ⟨p, 0, t⟩ :: acc
    return g.closure nl fst acc
  let mut states : Array (List Item) := #[initItems]
  let mut incoming : Array (Option GSym) := #[none]
  let mut transitions : Array (List (GSym × Nat)) := #[[]]
  -- find-or-add a state, returning its index
  let mut frontier : List Nat := [0]
  while !frontier.isEmpty do
    let si := frontier.head!
    frontier := frontier.tail!
    let items := states.getD si []
    for x in g.nextSymbols items do
      let tItems := g.goto nl fst items x
      -- find existing
      let mut found : Option Nat := none
      for j in [0:states.size] do
        if itemsEq (states.getD j []) tItems then found := some j
      match found with
      | some j => transitions := transitions.set! si ((x, j) :: transitions.getD si [])
      | none =>
          let j := states.size
          states := states.push tItems
          incoming := incoming.push (some x)
          transitions := transitions.push []
          transitions := transitions.set! si ((x, j) :: transitions.getD si [])
          frontier := j :: frontier
  let numStates := states.size
  -- action table
  let mkAction (si : Nat) : GAction := Id.run do
    let items := states.getD si []
    let trans := transitions.getD si []
    let shifts : List (Nat × Nat) := trans.filterMap (fun (x, t) =>
      match x with | .term tm => some (tm, t) | _ => none)
    let completes : List (Nat × Nat) := items.filterMap (fun it =>
      if it.dot == (g.rhsOf it.prod).size then some (it.la, it.prod) else none)
    let reduceProds : List Nat := completes.foldl (fun acc (_, p) =>
      if acc.contains p then acc else p :: acc) []
    if shifts.isEmpty && reduceProds.length == 1 then
      return GAction.defaultReduce (reduceProds.head!)
    else
      let arr : Array GLookahead := Id.run do
        let mut a : Array GLookahead := Array.replicate g.numTerm GLookahead.fail
        for (tm, t) in shifts do
          if tm < g.numTerm then a := a.set! tm (GLookahead.shift t)
        for (la, p) in completes do
          if la < g.numTerm && (a.getD la GLookahead.fail matches GLookahead.fail) then
            a := a.set! la (GLookahead.reduce p)
        return a
      return GAction.lookahead arr
  let action : Array GAction := (Array.range numStates).map mkAction
  -- goto table
  let gotoTab : Array (Array (Option Nat)) := (Array.range numStates).map (fun si =>
    let trans := transitions.getD si []
    (Array.range g.numNonterm).map (fun nt =>
      (trans.find? (fun (x, _) => x == GSym.nonterm nt)).map Prod.snd))
  -- predecessors
  let preds : Array (List Nat) := Id.run do
    let mut p : Array (List Nat) := Array.replicate numStates []
    for si in [0:numStates] do
      for (_, t) in transitions.getD si [] do
        p := p.set! t (si :: p.getD t [])
    return p
  -- past_symb fixpoint
  let headShapeOf (pastSymb : Array (List GSym)) (s : Nat) : List GSym :=
    if s == 0 then []
    else match incoming.getD s none with
         | some x => x :: pastSymb.getD s []
         | none => []
  let pastSymb : Array (List GSym) := Id.run do
    let mut cur : Array (List GSym) := Array.replicate numStates []
    let mut changed := true
    while changed do
      changed := false
      for s in [1:numStates] do
        let new := commonPrefixSymAll ((preds.getD s []).map (headShapeOf cur))
        if new != cur.getD s [] then cur := cur.set! s new; changed := true
    return cur
  -- past_state fixpoint (parallel state-sets); one level longer than past_symb so
  -- the validator can pin the state reached after popping the whole RHS.
  let stateHeadShapeOf (pastState : Array (List (List Nat))) (s : Nat) : List (List Nat) :=
    [s] :: pastState.getD s []
  let pastState : Array (List (List Nat)) := Id.run do
    let mut cur : Array (List (List Nat)) := Array.replicate numStates []
    let mut changed := true
    while changed do
      changed := false
      for s in [1:numStates] do
        let merged : List (List Nat) :=
          match (preds.getD s []).map (stateHeadShapeOf cur) with
          | [] => []
          | h :: t => t.foldl mergeStateSets h
        let truncated := merged.take ((pastSymb.getD s []).length + 1)
        if truncated != cur.getD s [] then cur := cur.set! s truncated; changed := true
    return cur
  return {
    numTerm := g.numTerm
    numNonterm := g.numNonterm
    numProd := g.numProd
    numStates := numStates
    startNonterm := g.start
    prodLhs := (Array.range g.numProd).map g.lhsOf
    prodRhsRev := (Array.range g.numProd).map (fun p => (g.rhsOf p).reverse)
    incoming := incoming
    action := action
    goto := gotoTab
    pastSymb := pastSymb.map (fun l => l.toArray)
    pastStateSets := pastState.map (fun l => (l.map List.toArray).toArray)
    nullable := nl
    first := fst.map List.toArray
    items := states.map (fun its => (its.map (fun it => (it.prod, it.dot, it.la))).toArray)
  }

end Grammar0

/-! ### Emitting concrete tables as Lean source

The generator is `partial`, so its output does not reduce in the kernel. To get
a kernel-`decide`-able certificate (no `native_decide` / no compiler-trust
axiom), we emit the computed `GenTables` as a concrete Lean literal that is then
checked into the example. Fields are newline-separated (Lean's comma-separated
struct literals are whitespace-flaky on large nested values). -/

private def emitGSym : GSym → String
  | .term i => s!".term {i}"
  | .nonterm i => s!".nonterm {i}"

private def emitGLook : GLookahead → String
  | .shift n => s!".shift {n}"
  | .reduce n => s!".reduce {n}"
  | .fail => ".fail"

private def emitGAction : GAction → String
  | .defaultReduce n => s!".defaultReduce {n}"
  | .lookahead a => "(.lookahead #[" ++ ", ".intercalate (a.toList.map emitGLook) ++ "])"

private def emitArr {α : Type} (f : α → String) (a : Array α) : String :=
  "#[" ++ ", ".intercalate (a.toList.map f) ++ "]"

private def emitNatArr (a : Array Nat) : String := emitArr toString a
private def emitOptGSym : Option GSym → String
  | none => "none" | some s => s!"(some ({emitGSym s}))"

/-- Emit a `GenTables` as a `def name : GenTables := …` source string. -/
def emitTables (name : String) (g : GenTables) : String :=
  let line (k v : String) := s!"    {k} := {v}\n"
  let arrArr {α} (f : α → String) (aa : Array (Array α)) : String :=
    emitArr (emitArr f) aa
  "def " ++ name ++ " : Gen.GenTables :=\n  {\n"
  ++ line "numTerm" (toString g.numTerm)
  ++ line "numNonterm" (toString g.numNonterm)
  ++ line "numProd" (toString g.numProd)
  ++ line "numStates" (toString g.numStates)
  ++ line "startNonterm" (toString g.startNonterm)
  ++ line "prodLhs" (emitNatArr g.prodLhs)
  ++ line "prodRhsRev" (arrArr emitGSym g.prodRhsRev)
  ++ line "incoming" (emitArr emitOptGSym g.incoming)
  ++ line "action" (emitArr emitGAction g.action)
  ++ line "goto" (emitArr (emitArr (fun (o : Option Nat) => match o with
        | none => "none" | some n => s!"(some {n})")) g.goto)
  ++ line "pastSymb" (arrArr emitGSym g.pastSymb)
  ++ line "pastStateSets" (emitArr (emitArr emitNatArr) g.pastStateSets)
  ++ line "nullable" (emitArr (fun b => if b then "true" else "false") g.nullable)
  ++ line "first" (emitArr emitNatArr g.first)
  ++ line "items" (emitArr (emitArr (fun (it : Nat × Nat × Nat) =>
        s!"({it.1}, {it.2.1}, {it.2.2})")) g.items)
  ++ "  }\n"

end Gen
end LeanMenhir
