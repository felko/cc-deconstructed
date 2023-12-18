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
        let x : Q($α) := decl.toExpr
        let fv : Q(Finset (Atom $β)) := q(($instFreeVariables).fv $x)
        return q($acc ∪ $fv)
    | _ => return acc

def evalPickFresh {i : Q(CC)} {qβ : Q(VarCat $i)} (x : TSyntax `ident) (qL : Q(Finset (Atom $qβ))) := do
  let FrIdent := mkIdent (.str (.str .anonymous x.getId.toString) "Fresh")
  let L ← runTermElab qL.toSyntax
  evalTactic (← `(tactic|
    cases (Atom.freshFor $L);
    rename_i $x:ident $FrIdent:ident;
    try simp only [Finset.union_empty,Finset.empty_union,Finset.union_assoc,FreeVariables.fv,id] at $FrIdent:ident;
  ))

syntax (name := gather_atoms)
  "gather_atoms" ident ":" term : tactic

elab_rules (kind := gather_atoms) : tactic
  | `(tactic| gather_atoms $x:ident : $β:term) =>
      withMainContext do
        let qi : Q(CC) ← mkFreshExprMVar (type? := q(CC))
        let qβ : Q(VarCat $qi) ← runTermElab (elabTerm β (expectedType? := q(VarCat $qi)))
        let qL : Q(Finset (Atom $qβ)) ← @gatherAtoms qi qβ
        let L ← runTermElab qL.toSyntax
        evalTactic (← `(tactic|
          let $x:ident := $L;
          try simp only [Finset.union_empty,Finset.empty_union,Finset.union_assoc,FreeVariables.fv,id] at $x:ident
        ))

syntax (name := pick_fresh)
  "pick_fresh" ident (":" term)? ("∉" term)? : tactic

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

structure ScopeInfo where
  i : Q(CC)
  α : Q(VarCat $i)
  x : TSyntax `ident
  L : Q(Finset (Atom $α))
  decl : LocalDecl

def findScope : TacticM (Option ScopeInfo) :=
  withMainContext do
    (← MonadLCtx.getLCtx).findDeclM? fun decl => do
      let ty : Q(Prop) :=
        match decl with
        | LocalDecl.cdecl (type := t) .. => t
        | LocalDecl.ldecl (type := t) .. => t
      -- dbg_trace (← ppExpr ty).pretty
      match ty with
      | ~q(∀ x, ¬(@Membership.mem _ _ ⟨_⟩ x $L) → ($p : Atom $α → Prop) x) => do
          let x : Name := match ty with | .forallE x _ _ _ => x | _ => .anonymous
          let xIdent : TSyntax `ident := mkIdent x
          return .some ⟨_, α, xIdent, L, decl⟩
      | _ => return .none

def specializeAnyScope : TacticM Unit := do
  match (← findScope) with
  | .some ⟨qi, qα, x, _, decl⟩ => do
      let FrIdent := mkIdent (.str (.str .anonymous x.getId.toString) "Fresh")
      let qL : Q(Finset (Atom $qα)) ← @gatherAtoms qi qα
      let declIdent := mkIdent decl.userName
      evalTactic (← `(tactic|
        cases (Atom.freshFor $(← runTermElab qL.toSyntax));
        rename_i $x:ident $FrIdent:ident;
        simp only [Finset.union_empty,Finset.empty_union,Finset.union_assoc,FreeVariables.fv,id] at $FrIdent:ident;
        specialize $declIdent:ident $x:ident (by aesop);
      ))
  | .none => throwTacticEx `specializeAllScopes (← getMainGoal) "couldn't find any goal to specialize"

syntax (name := decide)
  "decide" ident ":" term : tactic

elab_rules (kind := decide) : tactic
  | `(tactic| decide $x:ident : $t:term) =>
      withMainContext do
        evalTactic (← `(tactic|
          cases $x:ident : decide $t:term
            <;> first | replace $x:ident : ¬$t:term := of_decide_eq_false $x:ident
                      | replace $x:ident : $t:term := of_decide_eq_true $x:ident
            <;> simp [$x:ident] at *
        ))

namespace Playground
  scoped syntax (name := pick_fresh_any) "pick_fresh_any" : tactic
  elab_rules (kind := pick_fresh_any) : tactic
    | `(tactic| pick_fresh_any) =>
        withMainContext do
          let _ ← specializeAnyScope
          return ()

  variable
    (i : CC)
    (e1 e2 : Exp i)
    (z : Atom (.var i)) (Z1 Z2 : Atom (.tvar i))
    (L1 : Finset (Atom (.var i)))
    (L2 : Finset (Atom (.tvar i)))
    (inst : ∀ {α : VarCat i}, Atom α → Exp i → Exp i)
    (P : Exp i → Prop)
    (IH1 : ∀ x, x ∉ L1 → P (inst x e1))
    (IH2 : ∀ Y, Y ∉ L2 → P (inst Y e2))

  example (x y : Nat) : True := by
    decide h : x = y
    simp

  example : True := by
    -- IH1: ∀ x ∉ L1, P (inst x e1)
    -- IH2: ∀ Y ∉ L2, P (inst Y e2)
    pick_fresh_any
    -- IH2: ∀ Y ∉ L2, P (inst Y e2)
    -- x: Atom (VarCat.var i)
    -- IH1: P (inst x e1)
    -- x.Fresh: x ∉ L1
    pick_fresh_any
    -- x: Atom (VarCat.var i)
    -- IH1: P (inst x e1)
    -- x.Fresh: x ∉ L1
    -- Y: Atom (VarCat.tvar i)
    -- IH2: P (inst Y e2)
    -- Y.Fresh: Y ∉ L2
    constructor

  attribute [aesop safe tactic] specializeAnyScope

  example : ∃ x ∉ L1, P (inst x e1) := by aesop
end Playground
