import CCDeconstructed.Var
import CCDeconstructed.Syntax
import CCDeconstructed.CC

import Mathlib.Data.Finset.Fold
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.AList

open Feature VarCat

inductive Binding : VarCat i -> Type :=
  | val : Typ i -> Binding (var i)
  | sub : Typ i -> Binding (tvar i)
  | typ [HasFeature i type_bindings] : Typ i -> Binding (tvar i)

set_option genInjectivity false
structure Binder (i : CC) where
  cat : VarCat i
  name : Atom cat
  deriving DecidableEq

namespace Binder
  def freeVariablesVar (b : Binder i) : Finset (Atom (var i)) :=
    match b with
    | ⟨var _, x⟩ => {x}
    | ⟨tvar _, _⟩ => ∅

  def freeVariablesTVar (b : Binder i) : Finset (Atom (tvar i)) :=
    match b with
    | ⟨var _, _⟩ => ∅
    | ⟨tvar _, X⟩ => {X}

  instance : FreeVariables (Binder i) (var i) where
    fv := freeVariablesVar

  instance : FreeVariables (Binder i) (tvar i) where
    fv := freeVariablesTVar
end Binder

inductive Assoc (i : CC) : Type where
  | var : Atom (var i) -> Typ i -> Assoc i
  | sub : Atom (tvar i) -> Typ i -> Assoc i
  | typ [HasFeature i type_bindings] : Atom (tvar i) -> Typ i -> Assoc i

namespace Assoc
  infix:65 " ⦂ " => Assoc.var
  infix:65 " <: " => Assoc.sub
  infix:65 " ≔ " => Assoc.typ

  def fromSigma (p : (v : Binder i) × Binding v.cat) : Assoc i :=
    match p with
    | ⟨⟨.var _, x⟩, .val T⟩ => .var x T
    | ⟨⟨.tvar _, X⟩, .sub S⟩ => .sub X S
    | ⟨⟨.tvar _, X⟩, @Binding.typ _ _ T⟩ => .typ X T

  lemma fromSigma_inj :
      Assoc.fromSigma p1 = Assoc.fromSigma p2 →
      p1 = p2
    := by
      intros eq
      cases p1; rename_i x b1; cases p2; rename_i y b2
      cases x; rename_i c x; cases y; rename_i d y
      cases b1 <;> cases b2 <;> rename_i T U <;> cases eq <;> rfl

  def freeVariablesVar (a : Assoc i) : Finset (Atom (.var i)) :=
    match a with
    | .var x _ => {x}
    | .sub _ _ => ∅
    | @Assoc.typ _ _ _ _ => ∅

  def freeVariablesTVar (a : Assoc i) : Finset (Atom (.tvar i)) :=
    match a with
    | .var _ _ => ∅
    | .sub X _ => {X}
    | @Assoc.typ _ _ X _ => {X}

  instance : FreeVariables (Assoc i) (.var i) where
    fv := freeVariablesVar

  instance : FreeVariables (Assoc i) (.tvar i) where
    fv := freeVariablesTVar
end Assoc

abbrev Env (i : CC) := AList (fun (v : Binder i) => Binding v.cat)

namespace Env
  def cons (Γ : Env i) (a : Assoc i) : Env i :=
    match a with
    | .var x T => AList.insert ⟨var i, x⟩ (Binding.val T) Γ
    | .sub X S => AList.insert ⟨tvar i, X⟩ (Binding.sub S) Γ
    | @Assoc.typ _ _ X T => AList.insert ⟨tvar i, X⟩ (Binding.typ T) Γ

  infixl:60 " ▷ " => Env.cons

  def assocs (Γ : Env i) : Finset (Assoc i) :=
    Finset.mk
      (Multiset.ofList (Γ.entries.map Assoc.fromSigma))
      (List.Nodup.map_on fromSigma_inj_Γ nodupKeys_nodupEntries)
  where
      nodupKeys_nodupEntries : Γ.entries.Nodup := by
        cases Γ; rename_i entries nodupKeys
        simp [AList.keys] at nodupKeys
        induction entries <;> simp
        case cons head tail IH =>
          cases head; rename_i x b; simp at nodupKeys
          cases nodupKeys; rename_i xNotInTail nodupTail
          apply And.intro
          · intros H
            apply xNotInTail
            simp [List.keys] at *
            exists b
          · apply IH
            apply nodupTail

      fromSigma_inj_Γ :
        ∀ x ∈ Γ.entries, ∀ y ∈ Γ.entries,
        Assoc.fromSigma x = Assoc.fromSigma y
        → x = y
      := by
        intros
        apply Assoc.fromSigma_inj
        assumption

  def binders (Γ : Env i) : Finset (Binder i) :=
    Finset.mk (Multiset.ofList Γ.keys) Γ.nodupKeys

  def dom (Γ : Env i) (α : VarCat i) [FreeVariables (Binder i) α] : Finset (Atom α) :=
    Finset.fold (fun s t => s ∪ t) ∅ FreeVariables.fv Γ.binders

  instance instEmptyCollection : EmptyCollection (Env i) where
    emptyCollection := ∅

  instance instAssocMembership : Membership (Assoc i) (Env i) :=
    ⟨fun a Γ => a ∈ Γ.assocs⟩
end Env

attribute [irreducible] Env

instance : EmptyCollection (Env i) := Env.instEmptyCollection
instance : Membership (Assoc i) (Env i) := Env.instAssocMembership
