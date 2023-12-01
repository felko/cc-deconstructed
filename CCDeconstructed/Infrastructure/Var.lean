import CCDeconstructed.Syntax
import CCDeconstructed.Classes

open Scoped FreeVariables VarCat

namespace Var
  instance {α : VarCat i} : Coe (Atom α) (Var α) where
    coe := Var.free

  instance {α : VarCat i} : Coe (Index α) (Var α) where
    coe := Var.bound

  @[aesop norm]
  def fv {α : VarCat i} : Var α → Finset (Atom α)
      | .free x => {x}
      | .bound _ => ∅
      | .cap => ∅

  @[aesop norm]
  def bv {α : VarCat i} : Var α → Finset (Index α)
    | .free _ => ∅
    | .bound i => {i}
    | .cap => ∅

  @[simp,aesop norm]
  def subst {i : CC} {α : VarCat i} {β : Type} [Coe (Var α) β] (v : Var α) (x : Var α) (u : β) : β :=
    if v = x then u else v

  @[aesop norm]
  def substitute {i : CC} {α : VarCat i} (v : Var α) (x : Atom α) (u : Var α) : Var α :=
    @subst i α (Var α) ⟨id⟩ v (.free x) u

  @[aesop norm]
  def instantiateRec {i} {α : VarCat i} (v : Var α) (k : Index α) (u : Var α) : Var α :=
    @subst i α (Var α) ⟨id⟩ v (.bound k) u

  @[simp]
  instance instFreeVariables : FreeVariables (Var α) α where
    fv := fv

  @[aesop norm]
  def WellScopedRec {i : CC} {α : VarCat i} {allowCap : Bool} (n : Nat) : Var α → Prop
    | .bound k => k < n
    | .free _ => True
    | .cap => if allowCap then True else False

  @[aesop norm]
  def WellScoped {i : CC} {α : VarCat i} {allowCap : Bool} : Var α → Prop
    | .bound _ => False
    | .free _ => True
    | .cap => if allowCap then True else False

  @[aesop safe apply]
  lemma WellScoped_implies_WellScopedRec_0 {i : CC} {α : VarCat i} {v : Var α} {allowCap : Bool} :
    WellScoped (allowCap := allowCap) v →
    WellScopedRec (allowCap := allowCap) 0 v
  := by simp [WellScoped,WellScopedRec]

  @[aesop safe apply]
  lemma WellScopedRec_weaken {i : CC} {α : VarCat i} {v : Var α} {allowCap : Bool} :
    m <= n →
    WellScopedRec (allowCap := allowCap) m v →
    WellScopedRec (allowCap := allowCap) n v
  := by
    simp [WellScopedRec]
    intros
    cases v
    · case free => simp
    · case bound => simp [Index] at *; linarith
    · case cap => cases allowCap <;> simp at *

  @[simp]
  instance instWellScopedness (allowCap : Bool) {α : VarCat i} : WellScopedness (Var α) where
    WellScoped := WellScoped (allowCap := allowCap)
    WellScopedRec := WellScopedRec (allowCap := allowCap)

  @[simp]
  instance instWellScopednessInfrastructure (allowCap : Bool) {α : VarCat i} : WellScopedness.Infrastructure (Var α) where
    toWellScopedness := instWellScopedness allowCap
    WellScoped_implies_WellScopedRec_0 := WellScoped_implies_WellScopedRec_0 (allowCap := allowCap)
    WellScopedRec_weaken := WellScopedRec_weaken (allowCap := allowCap)

  @[aesop safe apply]
  lemma substitute_fresh :
    x ∉ fv v →
    substitute v x u = v
  := by simp [fv,substitute]; aesop

  @[aesop safe apply]
  lemma WellScopedRec_instantiateRec :
    WellScopedRec (allowCap := allowCap) n (instantiateRec v n u) →
    WellScopedRec (allowCap := allowCap) (n + 1) v
  := by
    simp [WellScopedRec]
    intros WS
    cases v
    · case free => simp
    · case bound k =>
      simp [instantiateRec] at *
      cases decEq k n <;> rename_i H <;> simp [H,Index] at *
      linarith
    · case cap =>
      simp [instantiateRec] at *
      assumption

  @[aesop safe apply]
  lemma instantiateRec_WellScopedRec :
    WellScopedRec (allowCap := allowCap) n v →
    k >= n →
    instantiateRec v k u = v
  := by
    simp [instantiateRec,WellScopedRec]
    intros WS leq v.Bound
    cases v <;> simp [Index] at *
    case bound k => exfalso; linarith

  @[simp]
  instance instScoped (allowCap : Bool) : Scoped (Var (.var i)) (.var i) where
    instantiateRec := instantiateRec
    substitute := substitute

  @[simp]
  instance instScopedInfrastructure (allowCap : Bool) : Scoped.Infrastructure (Var (.var i)) (.var i) where
    WellScopedRec := WellScopedRec
    WellScopedRec_weaken := WellScopedRec_weaken
    WellScoped_implies_WellScopedRec_0 := WellScoped_implies_WellScopedRec_0
    instantiateRec := instantiateRec
    substitute := substitute
    substitute_fresh := substitute_fresh
    WellScopedRec_instantiateRec := by
      intros n v u WS
      simp [Scoped.instantiateRec] at *
      apply WellScopedRec_instantiateRec (allowCap := allowCap)
      apply WS
    instantiateRec_WellScopedRec := by
      intros n v m u WS leq
      simp [Scoped.instantiateRec] at *
      apply instantiateRec_WellScopedRec (allowCap := allowCap) (n := n) (u := u)
      · apply WS
      · apply leq
end Var
