import CCDeconstructed.Syntax
import CCDeconstructed.Classes
import CCDeconstructed.Tactics
import CCDeconstructed.Infrastructure.Typ

set_option linter.unusedVariables false

open Scoped FreeVariables VarCat

namespace Binder
  instance instFreeVariables {α : VarCat i} : FreeVariables (Binder i) α where
    fv := Binder.dom
end Binder

namespace Assoc
  def freeVariables {α : VarCat i} (a : Assoc i) : Finset (Atom α) :=
    match α with
    | .var _ => Typ.freeVariablesVar (Assoc.type a)
    | .tvar _ => Typ.freeVariablesTyp (Assoc.type a)

  instance instFreeVariables {α : VarCat i} : FreeVariables (Assoc i) α where
    fv := freeVariables

  @[simp]
  def WellScopedRec (n : Nat) (a : Assoc i) : Prop :=
    Typ.WellScopedRec n (type a)

  @[simp]
  def WellScoped (a : Assoc i) : Prop :=
    Typ.WellScoped (type a)

  lemma WellScoped_implies_WellScopedRec_0 :
    WellScoped a →
    WellScopedRec 0 a
  := by
    simp [type]
    cases a <;> simp <;> apply Typ.WellScoped_implies_WellScopedRec_0

  lemma WellScopedRec_weaken :
    m ≤ n →
    WellScopedRec m a →
    WellScopedRec n a
  := by
    simp [type]
    cases a <;> simp <;> apply Typ.WellScopedRec_weaken

  instance instWellScopedness : WellScopedness (Assoc i) where
    WellScopedRec := WellScopedRec
    WellScoped := WellScoped
    WellScoped_implies_WellScopedRec_0 := WellScoped_implies_WellScopedRec_0
    WellScopedRec_weaken := WellScopedRec_weaken
end Assoc

namespace Env
  def freeVariables {α : VarCat i} (Γ : Env i) : Finset (Atom α) :=
    List.foldr (init := ∅) (Assoc.freeVariables · ∪ ·) Γ.assocs

  instance instFreeVariables {α : VarCat i} : FreeVariables (Env i) α where
    fv := freeVariables

  @[simp]
  def WellScopedRec (n : Nat) (Γ : Env i) : Prop :=
    Γ.assocs.Forall (Assoc.WellScopedRec n)

  @[simp]
  def WellScoped (Γ : Env i) : Prop :=
    Γ.assocs.Forall Assoc.WellScoped

  lemma WellScoped_implies_WellScopedRec_0 :
    WellScoped Γ →
    WellScopedRec 0 Γ
  := List.Forall.imp (@Assoc.WellScoped_implies_WellScopedRec_0 _)

  lemma WellScopedRec_weaken :
    m ≤ n →
    WellScopedRec m a →
    WellScopedRec n a
  := fun leq => List.Forall.imp (fun _ WS => Assoc.WellScopedRec_weaken leq WS)

  instance instWellScopedness : WellScopedness (Env i) where
    WellScopedRec := WellScopedRec
    WellScoped := WellScoped
    WellScoped_implies_WellScopedRec_0 := WellScoped_implies_WellScopedRec_0
    WellScopedRec_weaken := WellScopedRec_weaken
end Env
