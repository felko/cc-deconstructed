import CCDeconstructed.Syntax
import CCDeconstructed.Classes

open Scoped FreeVariables VarCat

namespace Var
  instance : Coe (Atom α) (Var α) where
    coe := Var.free

  instance : Coe (Index α) (Var α) where
    coe := Var.bound

  @[aesop norm]
  def fv : Var α → Finset (Atom α)
      | .free x => {x}
      | .bound _ => ∅
      | .cap => ∅

  @[aesop norm]
  def bv : Var α → Finset (Index α)
    | .free _ => ∅
    | .bound i => {i}
    | .cap => ∅

  @[simp,aesop norm]
  def subst [Coe (Var α) β] (v : Var α) (x : Var α) (u : β) : β :=
    if v = x then u else v

  @[aesop norm]
  def substitute {i} {α : VarCat i} (v : Var α) (x : Atom α) (u : Var α) : Var α :=
    @subst i α (Var α) ⟨id⟩ v (.free x) u

  @[aesop norm]
  def instantiateRec {i} {α : VarCat i} (v : Var α) (k : Index α) (u : Var α) : Var α :=
    @subst i α (Var α) ⟨id⟩ v (.bound k) u

  instance instFreeVariables : FreeVariables (Var α) α where
    fv := fv

  @[aesop norm]
  def WellScopedRec {i : CC} {α : VarCat i} (allowCap := false) (n : Nat) : Var α → Prop
    | .bound k => k < n
    | .free _ => True
    | .cap => if allowCap then True else False

  @[aesop norm]
  def WellScoped {i : CC} {α : VarCat i} (allowCap := false) : Var α → Prop
    | .bound _ => False
    | .free _ => True
    | .cap => if allowCap then True else False

  @[aesop safe apply]
  lemma WellScoped_implies_WellScopedRec_0 :
    WellScoped allowCap t →
    WellScopedRec allowCap 0 t
  := by simp [WellScoped,WellScopedRec]

  @[aesop safe apply]
  lemma WellScopedRec_weaken :
    m <= n →
    WellScopedRec allowCap m v →
    WellScopedRec allowCap n v
  := by
    simp [WellScopedRec]
    intros
    cases v
    · case free => simp
    · case bound => simp [Index] at *; linarith
    · case cap => cases allowCap <;> simp at *

  instance instWellScopedness (allowCap : Bool) : WellScopedness (Var α) where
    WellScopedRec := WellScopedRec allowCap
    WellScoped := WellScoped allowCap
    WellScoped_implies_WellScopedRec_0 := WellScoped_implies_WellScopedRec_0
    WellScopedRec_weaken := WellScopedRec_weaken

  @[aesop safe apply]
  lemma substitute_fresh :
    x ∉ fv v →
    substitute v x u = v
  := by simp [fv,substitute]; aesop

  @[aesop safe apply]
  lemma WellScopedRec_instantiateRec :
    WellScopedRec allowCap n (instantiateRec v n u)→
    WellScopedRec allowCap (n + 1) v
  := by
    simp [WellScopedRec]
    intros WS
    cases v
    · case free => simp
    · case bound k =>
      simp [instantiateRec] at *
      cases (decEq k n) <;> rename_i H <;> simp [H,Index] at *
      linarith
    · case cap =>
      simp [instantiateRec] at *
      assumption

  @[aesop safe apply]
  lemma instantiateRec_WellScopedRec :
    WellScopedRec allowCap n v →
    k >= n →
    instantiateRec v k u = v
  := by
    simp [instantiateRec,WellScopedRec]
    intros WS leq v.Bound
    cases v <;> simp [Index] at *
    case bound k => exfalso; linarith

  instance instScoped (allowCap : Bool) : Scoped (Var (.var i)) (.var i) where
    instantiateRec := instantiateRec
    substitute := substitute
    substitute_fresh := substitute_fresh
    WellScopedRec_instantiateRec := WellScopedRec_instantiateRec (allowCap := allowCap)
    instantiateRec_WellScopedRec := instantiateRec_WellScopedRec (allowCap := allowCap)
    WellScoped_implies_WellScopedRec_0 := WellScoped_implies_WellScopedRec_0
    WellScopedRec_weaken := WellScopedRec_weaken
end Var
