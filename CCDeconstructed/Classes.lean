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

namespace WellScopedness
  attribute [simp,aesop norm unfold] WellScopedRec WellScoped

  class Infrastructure (α : Type) extends WellScopedness α where
    WellScopedRec0 :
      WellScoped t →
      WellScopedRec 0 t
    weaken :
      m <= n →
      WellScopedRec m t →
      WellScopedRec n t
end WellScopedness

class FreeVariables (α : Type) (β : VarCat i) where
  fv : α → Finset (Atom β)

namespace FreeVariables
  attribute [simp,aesop norm unfold] fv

  instance instAtom : FreeVariables (Atom α) α := ⟨singleton⟩
  instance instFinsetAtom : FreeVariables (Finset (Atom α)) α := ⟨id⟩
  instance instFinsetFreeVariables [FreeVariables α β] : FreeVariables (Finset α) β := ⟨fun s => s.fold (· ∪ ·) ∅ fv⟩
end FreeVariables

open FreeVariables

@[simp,aesop norm unfold]
abbrev VarCat.type (α : VarCat i) : Type :=
  match α with
  | .var _ => Var (var i)
  | .tvar _ => Typ i

open VarCat

set_option synthInstance.checkSynthOrder false
class Scoped (α : Type) (β : VarCat i) extends FreeVariables α β where
  instantiateRec : α → Index β → β.type → α
  substitute : α → Atom β → β.type → α

namespace Scoped
  attribute [simp] instantiateRec substitute

  @[simp]
  def instantiate [Scoped α β] (t : α) (u : type β) : α :=
    instantiateRec t 0 u

  set_option synthInstance.checkSynthOrder false
  class Infrastructure (α : Type) (β : VarCat i) extends Scoped α β, WellScopedness.Infrastructure α where
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

  @[simp]
  lemma Instractructure.instantiateRec_WellScoped [self : Infrastructure α β] :
    self.WellScoped t →
    self.instantiateRec t k u = t
  := by
    intros H
    apply self.instantiateRec_WellScopedRec
    · apply self.WellScopedRec0 H
    · linarith

  attribute [aesop unsafe forward 20%]
    Infrastructure.substitute_fresh
    Infrastructure.instantiateRec_WellScopedRec
    Infrastructure.WellScopedRec_instantiateRec
end Scoped

set_option synthInstance.checkSynthOrder false
class WellFormedness (i : CC) (α : Type) extends WellScopedness α where
  WellFormed : Env i → α → Prop
  toWellScoped :
    WellFormed Γ t →
    WellScoped t
  weaken :
    WellFormed (Γ ++ Δ) t →
    Env.Nodup (Γ ++ Θ ++ Δ) →
    WellFormed (Γ ++ Θ ++ Δ) t

namespace WellFormedness
  lemma weaken_head {i : CC} [self : WellFormedness i α] {Γ Δ : Env i} {t : α} :
    WellFormed Γ t →
    Env.Nodup (Γ ++ Δ) →
    WellFormed (Γ ++ Δ) t
  := by
    intros WF Nodup
    conv in Γ ++ Δ =>
      rw [<- Env.concat_nil (Γ := Γ ++ Δ)]
      rfl
    apply weaken
      <;> assumption

  lemma weaken_cons {i : CC} [self : WellFormedness i α] {Γ : Env i} {a : Assoc i} {t : α} :
    Env.Nodup Γ →
    a.name ∉ Env.dom Γ →
    WellFormed Γ t →
    WellFormed (Γ ▷ a) t
  := by
    intros Nodup NotIn WF
    rw [<- Env.concat_singleton]
    apply weaken_head WF
    apply Env.Nodup.cons Nodup NotIn
end WellFormedness
