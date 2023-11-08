import Mathlib.Data.Finset.Basic

import CCDeconstructed.Var
import CCDeconstructed.Syntax
import CCDeconstructed.Classes

open Qq Lean Elab Tactic Term Meta

def gatherAtoms {i : Q(CC)} (β : Q(VarCat $i)) : TacticM Q(Finset (Atom $β)) := do
  (← MonadLCtx.getLCtx).foldrM (init := q(∅)) fun decl acc => do
    let α : Q(Type) :=
      match decl with
      | LocalDecl.cdecl (type := t) .. => t
      | LocalDecl.ldecl (type := t) .. => t
    match ← trySynthInstanceQ q(FreeVariables $α $β) with
    | .some instFreeVariables => do
        dbg_trace ("\tok!")
        let x : Q($α) := decl.toExpr
        let fv : Q(Finset (Atom $β)) := q(($instFreeVariables).fv $x)
        return q($acc ∪ $fv)
    | _ => return acc

def evalPickFresh {i : Q(CC)} {qβ : Q(VarCat $i)} (x : TSyntax `ident) (qL : Q(Finset (Atom $qβ))) := do
  let FrIdent := mkIdent (.str (.str .anonymous x.getId.toString) "Fresh")
  evalTactic (← `(tactic|
    cases (Atom.freshFor $(← runTermElab qL.toSyntax));
    rename_i $x:ident $FrIdent:ident;
    try simp only [Finset.union_empty,Finset.empty_union,Finset.union_assoc,FreeVariables.fv,id] at $FrIdent:ident;
  ))

syntax (name := pick_fresh)
  "pick_fresh" ident (":" term)? ("∉" term)? : tactic

/-
elab_rules (kind := pick_fresh) : tactic
  | `(tactic| pick_fresh $x:ident : $β:term) =>
      withMainContext do
        let qi : Q(CC) ← mkFreshExprMVar (type? := q(CC))
        let qβ : Q(VarCat $qi) ← runTermElab (elabTerm β (expectedType? := q(VarCat $qi)))
        let qL : Q(Finset (Atom $qβ)) ← @gatherAtoms qi qβ
        evalPickFresh x qL
  | `(tactic| pick_fresh $x:ident ∉ $L:term) =>
      withMainContext do
        let qi : Q(CC) ← mkFreshExprMVar (type? := q(CC))
        let qβ : Q(VarCat $qi) ← mkFreshExprMVar (type? := q(VarCat $qi))
        let qL : Q(Finset (Atom $qβ)) ← runTermElab (elabTerm L (expectedType? := q(Finset (Atom $qβ))))
        evalPickFresh x qL
-/

elab_rules (kind := pick_fresh) : tactic
  | `(tactic| pick_fresh $x:ident : $β:term) =>
      withMainContext do
        let qi : Q(CC) ← mkFreshExprMVar (type? := q(CC))
        let qβ : Q(VarCat $qi) ← runTermElab (elabTerm β (expectedType? := q(VarCat $qi)))
        let qL : Q(Finset (Atom $qβ)) ← @gatherAtoms qi qβ
        evalPickFresh x qL
  | `(tactic| pick_fresh $x:ident ∉ $L:term) =>
      withMainContext do
        let qi : Q(CC) ← mkFreshExprMVar (type? := q(CC))
        let qβ : Q(VarCat $qi) ← mkFreshExprMVar (type? := q(VarCat $qi))
        let qL : Q(Finset (Atom $qβ)) ← runTermElab (elabTerm L (expectedType? := q(Finset (Atom $qβ))))
        evalPickFresh x qL
