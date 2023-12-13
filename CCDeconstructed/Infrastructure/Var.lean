import CCDeconstructed.Syntax
import CCDeconstructed.Classes

open Scoped FreeVariables VarCat

namespace Var
  instance {α : VarCat i} : Coe (Atom α) (Var α) where
    coe := Var.free

  instance {α : VarCat i} : Coe (Index α) (Var α) where
    coe := Var.bound

  @[simp]
  def fv {α : VarCat i} : Var α → Finset (Atom α)
    | .free x => {x}
    | .bound _ => ∅
    | .cap => ∅

  @[simp]
  def bv {α : VarCat i} : Var α → Finset (Index α)
    | .free _ => ∅
    | .bound i => {i}
    | .cap => ∅

  @[simp]
  def subst {i : CC} {α : VarCat i} {β : Type} [Coe (Var α) β] (v : Var α) (x : Var α) (u : β) : β :=
    if v = x then u else v

  @[simp]
  def substitute {i : CC} {α : VarCat i} (v : Var α) (x : Atom α) (u : Var α) : Var α :=
    @subst i α (Var α) ⟨id⟩ v (.free x) u

  @[simp]
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

  namespace WellScoped
    @[aesop unsafe]
    lemma WellScopedRec0 {i : CC} {α : VarCat i} {v : Var α} {allowCap : Bool} :
      WellScoped (allowCap := allowCap) v →
      WellScopedRec (allowCap := allowCap) 0 v
    := by simp [WellScoped,WellScopedRec]

    @[aesop unsafe]
    lemma weaken {i : CC} {α : VarCat i} {v : Var α} {allowCap : Bool} :
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

    @[aesop unsafe]
    def map_allowCap {i : CC} {α : VarCat i} {allowCap₁ allowCap₂ : Bool} {v : Var α} :
      allowCap₁ ≤ allowCap₂ →
      WellScoped (allowCap := allowCap₁) v →
      WellScoped (allowCap := allowCap₂) v
    := by
      cases v
        <;> cases allowCap₁
        <;> cases allowCap₂
        <;> simp [Bool.instLEBool,WellScoped]

    @[simp]
    instance instWellScopedness (allowCap : Bool) {α : VarCat i} : WellScopedness (Var α) where
      WellScoped := WellScoped (allowCap := allowCap)
      WellScopedRec := WellScopedRec (allowCap := allowCap)

    @[simp]
    instance instWellScopednessInfrastructure (allowCap : Bool) {α : VarCat i} : WellScopedness.Infrastructure (Var α) where
      toWellScopedness := instWellScopedness allowCap
      WellScopedRec0 := WellScopedRec0 (allowCap := allowCap)
      weaken := weaken (allowCap := allowCap)
  end WellScoped

  @[aesop unsafe]
  lemma substitute_fresh :
    x ∉ fv v →
    substitute v x u = v
  := by simp [fv,substitute]; aesop

  @[aesop unsafe]
  lemma substitute_instantiateRec_intro :
    x ∉ fv v →
    instantiateRec v k u = substitute (instantiateRec v k x) x u
  := by cases v <;> simp [fv,substitute,instantiateRec] <;> aesop

  @[aesop unsafe]
  lemma fv_subset_fv_instantiateRec :
    fv v ⊆ fv (instantiateRec v k u)
  := by cases v <;> simp [fv,instantiateRec]

  @[aesop unsafe]
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

  @[aesop unsafe]
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
    toScoped := instScoped allowCap
    toInfrastructure := WellScoped.instWellScopednessInfrastructure allowCap
    substitute_fresh := substitute_fresh
    WellScopedRec_instantiateRec := WellScopedRec_instantiateRec
    instantiateRec_WellScopedRec := instantiateRec_WellScopedRec

  @[aesop unsafe]
  lemma substitute_instantiateRec {x : Atom (.var i)} {v : Var (.var i)} {u₁ : Var (.var i)} {k : Index (.var i)}  {u₂ : Var (.var i)} :
    Var.WellScoped (allowCap := allowCap) u₂ →
    substitute (instantiateRec v k u₁) x u₂ = instantiateRec (substitute v x u₂) k (Var.substitute u₁ x u₂)
  := by aesop

  @[aesop unsafe]
  lemma WellScoped_substitute {v : Var (.var i)} {x : Atom (.var i)} {u : Var (.var i)} :
    WellScoped (allowCap := allowCap) u →
    WellScoped (allowCap := allowCap) v →
    WellScoped (allowCap := allowCap) (substitute v x u)
  := by aesop
end Var
