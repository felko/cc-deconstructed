import CCDeconstructed.Syntax
import CCDeconstructed.Classes
import CCDeconstructed.Infrastructure.Var

open Scoped FreeVariables VarCat

set_option linter.unusedVariables false

namespace Cap
  @[aesop norm]
  def fv (C : Cap i) : Finset (Atom (var i)) :=
    C.fold (· ∪ ·) ∅ Var.fv

  @[aesop unsafe]
  lemma mem_free_iff_mem_fv :
    .free x ∈ C ↔ x ∈ fv C
  := by
    induction' C using Finset.induction <;> aesop

  @[aesop unsafe]
  lemma mem_free_implies_mem_fv :
    .free x ∈ C → x ∈ fv C
  := Iff.mp mem_free_iff_mem_fv

  @[aesop unsafe]
  lemma mem_fv_implies_mem_free :
    x ∈ fv C → .free x ∈ C
  := Iff.mpr mem_free_iff_mem_fv

  @[aesop norm]
  def bv (C : Cap i) : Finset (Index (var i)) :=
    C.fold (· ∪ ·) ∅ Var.bv

  @[aesop unsafe]
  lemma mem_bound_iff_mem_bv :
    .bound k ∈ C ↔ k ∈ bv C
  := by
    induction' C using Finset.induction <;> aesop

  @[aesop unsafe]
  lemma mem_bound_implies_mem_bv :
    .bound k ∈ C → k ∈ bv C
  := Iff.mp mem_bound_iff_mem_bv

  lemma mem_bv_implies_mem_bound :
    k ∈ bv C → .bound k ∈ C
  := Iff.mpr mem_bound_iff_mem_bv

  instance : FreeVariables (Cap i) (var i) where
    fv := fv

  @[simp]
  def instantiateRecCap (C : Cap i) (k : Index (var i)) (D : Cap i) :=
    if .bound k ∈ C then
      C \ {.bound k} ∪ D
    else
      C

  @[simp]
  def instantiateRecVar (C : Cap i) (k : Index (var i)) (u : Var (var i)) :=
    instantiateRecCap C k {u}

  @[simp]
  lemma instantiateRecCap_singleton_instantiateRecVar :
    instantiateRecCap C k {u} = instantiateRecVar C k u
  := rfl

  @[aesop norm 10]
  def substituteCap (C : Cap i) (x : Atom (var i)) (D : Cap i) :=
    if .free x ∈ C then
      C \ {.free x} ∪ D
    else
      C

  @[simp]
  def substituteVar (C : Cap i) (x : Atom (var i)) (u : Var (var i)) :=
    substituteCap C x {u}

  @[simp]
  lemma substituteCap_singleton_substituteVar :
    substituteCap C k {u} = substituteVar C k u
  := rfl

  @[aesop norm 5]
  def WellScopedRec (n : Nat) (C : Cap i) :=
    ∀ v ∈ C, Var.WellScopedRec (allowCap := true) n v

  @[aesop norm 5]
  def WellScoped (C : Cap i) :=
    ∀ v ∈ C, Var.WellScoped (allowCap := true) v

  namespace WellScoped
    @[aesop unsafe]
    lemma WellScopedRec0 :
      WellScoped C →
      WellScopedRec 0 C
    := by aesop

    @[aesop unsafe]
    lemma weaken :
      m <= n →
      WellScopedRec m C →
      WellScopedRec n C
    := by
      intros leq C.WS v v.In
      apply Var.WellScoped.weaken <;> aesop

    instance instWellScopednessInfrastructure : WellScopedness.Infrastructure (Cap i) where
      WellScopedRec := WellScopedRec
      WellScoped := WellScoped
      WellScopedRec0 := WellScopedRec0
      weaken := weaken
  end WellScoped

  @[aesop unsafe]
  lemma substituteCap_fresh :
    x ∉ fv C →
    substituteCap C x D = C
  := by
    simp [substituteCap]
    intros x.NotIn x.In
    exfalso; apply x.NotIn
    apply mem_free_implies_mem_fv x.In

  @[aesop unsafe]
  lemma substituteVar_fresh :
    x ∉ fv C →
    substituteVar C x u = C
  := substituteCap_fresh

  @[aesop unsafe]
  lemma substituteCap_instantiateRecCap_intro :
    x ∉ fv C →
    instantiateRecCap C k D = substituteCap (instantiateRecCap C k {.free x}) x D
  := by
    intros x.NotIn
    replace x.NotIn := mem_free_iff_mem_fv.not.mpr x.NotIn
    aesop

  @[aesop unsafe]
  lemma substituteVar_instantiateRecVar_intro :
    x ∉ fv C →
    instantiateRecVar C k u = substituteVar (instantiateRecVar C k x) x u
  := substituteCap_instantiateRecCap_intro

  @[aesop unsafe]
  lemma WellScopedRec_instantiateRecCap :
    WellScopedRec n (instantiateRecCap C n D) →
    WellScopedRec (n + 1) C
  := by
    simp only [instantiateRecCap,WellScopedRec]
    intros C.WS v v.WS
    split at C.WS
    · case inl In =>
      specialize C.WS v
      cases v <;> simp [Var.WellScopedRec] at *
      case bound k =>
      cases decEq k n
      · case isFalse Neq =>
        simp [Neq] at C.WS
        apply Nat.lt_add_right
        apply C.WS (Or.inl v.WS)
      · case isTrue Eq =>
        cases Eq
        simp at *
    · case inr NotIn =>
      exact Var.WellScoped.weaken (m := n) (by linarith) (C.WS v v.WS)

  @[aesop unsafe]
  lemma WellScopedRec_instantiateRecVar :
    WellScopedRec n (instantiateRecVar C n u) →
    WellScopedRec (n + 1) C
  := WellScopedRec_instantiateRecCap

  @[aesop unsafe]
  lemma instantiateRecCap_WellScopedRec :
    WellScopedRec n C →
    k >= n →
    instantiateRecCap C k D = C
  := by
    simp [WellScopedRec,Var.WellScopedRec,instantiateRecCap,Index]
    intros C.WS geq k.In
    specialize C.WS (.bound k) k.In
    simp at C.WS
    exfalso
    clear * - geq C.WS
    linarith

  @[aesop unsafe]
  lemma instantiateRecVar_WellScopedRec :
    WellScopedRec n C →
    k >= n →
    instantiateRecVar C k u = C
  := instantiateRecCap_WellScopedRec

  @[aesop unsafe]
  lemma mem_substituteCap :
    y' ∈ substituteCap C x D →
    ∃ y ∈ C, y' ∈ substituteCap {y} x D
  := by aesop

  @[aesop unsafe]
  lemma mem_substituteVar :
    y' ∈ substituteVar C x u →
    ∃ y ∈ C, y' ∈ substituteVar {y} x u
  := mem_substituteCap

  @[simp]
  lemma fv_union :
    fv (C ∪ D) = fv C ∪ fv D
  := by
    simp [fv]
    induction D using Finset.induction <;> simp
    case insert v D v.NotIn IH =>
    rw [IH]
    aesop

  @[simp]
  lemma fv_diff :
    fv (C \ D) = fv C \ fv D
  := by
    simp [fv,-Var.fv]
    induction C using Finset.induction <;> simp [-Var.fv]
    case insert v C v.NotInC IH =>
    cases Finset.decidableMem v D
    · case isFalse v.NotInD =>
      rw [Finset.insert_sdiff_of_not_mem _ v.NotInD]
      rw [Finset.fold_insert (by clear * - v.NotInC; aesop)]
      rw [IH]
      rw [Finset.union_sdiff_distrib]
      congr
      rw [(Finset.sdiff_eq_self (Var.fv v) (Finset.fold (fun x x_1 => x ∪ x_1) ∅ Var.fv D)).mpr]
      cases v <;> simp [Var.fv]
      case e_a.free x =>
      apply Finset.subset_iff.mpr
      intros y y.In
      simp at y.In
      simp
      obtain ⟨y.Eq, y.In⟩ := y.In
      cases y.Eq
      change x ∈ fv D at y.In
      apply v.NotInD
      apply mem_fv_implies_mem_free y.In
    · case isTrue v.InD =>
      simp at *
      rw [Finset.insert_sdiff_of_mem _ v.InD]
      rw [IH]
      change fv C \ fv D  = (Var.fv v ∪ fv C) \ fv D
      rw [Finset.union_sdiff_distrib]
      rw [<- Finset.empty_union (s := fv C \ fv D)]
      congr
      symm
      cases v <;> simp [Var.fv]
      · apply mem_free_implies_mem_fv v.InD
      · simp

  @[aesop unsafe]
  lemma fv_subset_fv_instantiateRecCap :
    fv C ⊆ fv (instantiateRecCap C k D)
  := by
    simp [instantiateRecCap]
    split
    · case inl k.In =>
      simp
      conv in fv {Var.bound k} =>
        simp [fv,Var.fv]
        rfl
      simp
      apply Finset.subset_union_left
    · case inr k.NotIn =>
      apply Finset.subset_of_eq rfl

  @[aesop unsafe]
  lemma fv_subset_fv_instantiateRecVar :
    fv C ⊆ fv (instantiateRecVar C k u)
  := fv_subset_fv_instantiateRecCap

  @[simp]
  instance instScopedInfrastructure : Scoped.Infrastructure (Cap i) (var i) where
    instantiateRec := instantiateRecVar
    substitute := substituteVar
    substitute_fresh := substituteVar_fresh
    WellScopedRec_instantiateRec := WellScopedRec_instantiateRecVar
    instantiateRec_WellScopedRec := instantiateRecVar_WellScopedRec

  instance instEmptyCollection : EmptyCollection (Cap i) := inferInstance
  instance instSingleton : Singleton (Var (.var i)) (Cap i) := inferInstance
  instance instMembership : Membership (Var (.var i)) (Cap i) := inferInstance

  @[aesop unsafe]
  lemma substituteCap_instantiateRecCap {x : Atom (.var i)} {D₁ : Cap i} {C : Cap i} {k : Index (.var i)}  {D₂ : Cap i} :
    Cap.WellScoped D₂ →
    substituteCap (instantiateRecCap C k D₁) x D₂ = instantiateRecCap (substituteCap C x D₂) k (substituteCap D₁ x D₂)
  := by
    intros D₂.WS
    simp [WellScoped,Var.WellScoped] at D₂.WS
    simp [substituteCap,instantiateRecCap]
    split
    · split
      · split
        · split
          · split
            · aesop
            · simp [*] at *
              have : Var.bound k ∉ D₂ := D₂.WS k
              aesop
          · aesop
        · aesop
      · aesop
    · split
      · split
        · simp [*] at *
          have : Var.bound k ∉ D₂ := D₂.WS k
          aesop
        · simp [*] at *
      · simp [*] at *

  @[aesop unsafe]
  lemma substituteVar_instantiateRecVar {x : Atom (.var i)} {D₁ : Var (.var i)} {C : Cap i} {k : Index (.var i)}  {u₂ : Var (.var i)} :
    Var.WellScoped (allowCap := allowCap) u₂ →
    substituteVar (instantiateRecVar C k u₁) x u₂ = instantiateRecVar (substituteVar C x u₂) k (Var.substitute u₁ x u₂)
  := by
    intros u₂.WS
    unfold substituteVar instantiateRecVar
    have Eq : {Var.substitute u₁ x u₂} = Cap.substituteCap {u₁} x {u₂} := by
      simp [Var.substitute,Cap.substituteCap]
      split
      · case inl Eq =>
        simp [Eq]
      · case inr Neq =>
        replace Neq : Var.free x ≠ u₁ := Neq ∘ Eq.symm
        simp [Neq]
    rw [Eq]
    apply substituteCap_instantiateRecCap
    simp [WellScoped]
    exact Var.WellScoped.map_allowCap (by simp) u₂.WS

  @[aesop unsafe]
  lemma WellScoped_substituteCap {C : Cap i} {x : Atom (.var i)} {D : Cap i} :
    WellScoped D →
    WellScoped C →
    WellScoped (substituteCap C x D)
  := by
    intros D.WS C.WS v v.In
    simp [substituteCap] at v.In
    split at v.In
    · case inl In =>
      simp at v.In
      rcases v.In with ⟨v.In, v.Neq⟩ | ⟨v.In⟩
      · apply C.WS v v.In
      · apply D.WS v v.In
    · case inr NotIn =>
      apply C.WS v v.In

  @[aesop unsafe]
  lemma WellScoped_substituteVar {C : Cap i} {x : Atom (.var i)} {u : Var (.var i)} :
    Var.WellScoped (allowCap := allowCap) u →
    WellScoped C →
    WellScoped (substituteVar C x u)
  := by
    intros u.WS C.WS
    apply WellScoped_substituteCap _ C.WS
    simp [WellScoped]
    exact Var.WellScoped.map_allowCap (by simp) u.WS
end Cap
