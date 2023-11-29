import Lean.Meta
import Lean.Meta.Tactic.Util
import Lean.Elab.Tactic

import Std.Classes.SetNotation

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith

import CCDeconstructed.Env

attribute [simp,aesop norm unfold] Coe.coe

class WellScopedness (α : Type) where
  WellScopedRec : Nat → α → Prop
  WellScoped := WellScopedRec 0
  WellScoped_implies_WellScopedRec_0 :
    WellScoped t → WellScopedRec 0 t
  WellScopedRec_weaken :
    m <= n →
    WellScopedRec m t →
    WellScopedRec n t

attribute [simp,aesop norm unfold]
  WellScopedness.WellScopedRec
  WellScopedness.WellScoped
attribute [aesop unsafe forward 50%]
  WellScopedness.WellScoped_implies_WellScopedRec_0
attribute [aesop unsafe forward 20%]
  WellScopedness.WellScopedRec_weaken

class FreeVariables (α : Type) (β : VarCat i) where
  fv : α → Finset (Atom β)

open FreeVariables

attribute [simp,aesop norm unfold] FreeVariables.fv

instance : FreeVariables (Atom α) α := ⟨singleton⟩
instance : FreeVariables (Finset (Atom α)) α := ⟨id⟩

@[simp,aesop norm unfold]
def VarCat.type (α : VarCat i) : Type :=
  match α with
  | .var _ => Var (var i)
  | .tvar _ => Typ i

open VarCat

set_option synthInstance.checkSynthOrder false
class Scoped (α : Type) (β : VarCat i) extends WellScopedness α, FreeVariables α β where
  instantiateRec : α → Index β → type β → α
  substitute : α → Atom β → type β → α
  substitute_fresh :
    x ∉ fv t →
    substitute t x u = t
  WellScopedRec_instantiateRec :
    WellScopedRec n (instantiateRec t n u) →
    WellScopedRec (n + 1) t
  instantiateRec_WellScopedRec :
    WellScopedRec n t →
    k >= n →
    instantiateRec t k u = t

attribute [simp]
  Scoped.instantiateRec
  Scoped.substitute
attribute [aesop unsafe forward 20%]
  Scoped.substitute_fresh
  Scoped.instantiateRec_WellScopedRec

@[simp]
def Scoped.instantiate [Scoped α β] (t : α) (u : type β) : α := instantiateRec t 0 u

@[simp]
lemma instantiateRec_WellScoped [s : Scoped α β] :
  s.WellScoped t →
  s.instantiateRec t k u = t
:= by
  intros H
  apply s.instantiateRec_WellScopedRec
  · apply s.WellScoped_implies_WellScopedRec_0 H
  · linarith

class WellFormedness (i : CC) (α : Type) extends WellScopedness α where
  WellFormed : Env i → α → Prop
  WellFormed_WellScoped :
    WellFormed Γ t →
    WellScoped t
  WellFormed_weaken :
    WellFormed Δ t →
    WellFormed (Γ ++ Δ) t
  WellFormed_weaken_head :
    WellFormed Γ t →
    WellFormed (Γ ▷ a) t
  := by
    apply WellForm
