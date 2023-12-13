import CCDeconstructed.Syntax
import CCDeconstructed.Classes
import CCDeconstructed.Tactics
import CCDeconstructed.Infrastructure.Typ

set_option linter.unusedVariables false

open Scoped FreeVariables VarCat

namespace Assoc
  def fvTyp (a : Assoc i) : Finset (Atom (.tvar i)) :=
    Assoc.dom a ∪ Typ.fvTyp (Assoc.type a)

  @[simp] lemma fvTyp_val : fvTyp (x ⦂  T) =       Typ.fvTyp T := by simp [fvTyp,dom]
  @[simp] lemma fvTyp_sub : fvTyp (X <: S) = {X} ∪ Typ.fvTyp S := by simp [fvTyp,dom]
  @[simp] lemma fvTyp_typ : fvTyp (X ≔  T) = {X} ∪ Typ.fvTyp T := by simp [fvTyp,dom]

  def fvVar (a : Assoc i) : Finset (Atom (.var i)) :=
    Assoc.dom a ∪ Typ.fvVar (Assoc.type a)

  @[simp] lemma fvVar_val : fvVar (x ⦂  T) = {x} ∪ Typ.fvVar T := by simp [fvVar,dom]
  @[simp] lemma fvVar_sub : fvVar (X <: S) =       Typ.fvVar S := by simp [fvVar,dom]
  @[simp] lemma fvVar_typ : fvVar (X ≔  T) =       Typ.fvVar T := by simp [fvVar,dom]

  instance instFreeVariablesTyp : FreeVariables (Assoc i) (.tvar i) where
    fv := fvTyp

  instance instFreeVariablesVar : FreeVariables (Assoc i) (.var i) where
    fv := fvVar

  def WellScopedRec (n : Nat) (a : Assoc i) : Prop :=
    Typ.WellScopedRec n (type a)

  def WellScoped (a : Assoc i) : Prop :=
    Typ.WellScoped (type a)

  namespace WellScoped
    lemma WellScopedRec0 :
      WellScoped a →
      WellScopedRec 0 a
    := by
      apply Typ.WellScoped.WellScopedRec0

    lemma weaken :
      m ≤ n →
      WellScopedRec m a →
      WellScopedRec n a
    := by
      apply Typ.WellScoped.weaken

    instance instWellScopedness : WellScopedness (Assoc i) where
      WellScopedRec := WellScopedRec
      WellScoped := WellScoped

    instance instWellScopednessInfrastructure : WellScopedness.Infrastructure (Assoc i) where
      WellScopedRec0 := WellScopedRec0
      weaken := weaken
  end WellScoped

  def instantiateRecTyp (a : Assoc i) (K : Index (.tvar i)) (U : Typ i) : Assoc i :=
    map (Typ.instantiateRecTyp · K U) a

  @[simp] lemma instantiateRecTyp_val : instantiateRecTyp (x ⦂  T) K U = x ⦂  Typ.instantiateRecTyp T K U := by simp [instantiateRecTyp]
  @[simp] lemma instantiateRecTyp_sub : instantiateRecTyp (X <: S) K U = X <: Typ.instantiateRecTyp S K U := by simp [instantiateRecTyp]
  @[simp] lemma instantiateRecTyp_typ : instantiateRecTyp (X ≔  T) K U = X ≔  Typ.instantiateRecTyp T K U := by simp [instantiateRecTyp]

  def substituteTyp (a : Assoc i) (X : Atom (.tvar i)) (U : Typ i) : Assoc i :=
    map (Typ.substituteTyp · X U) a

  @[simp] lemma substituteTyp_val : substituteTyp (x ⦂  T) Y U = x ⦂  Typ.substituteTyp T Y U := by simp [substituteTyp]
  @[simp] lemma substituteTyp_sub : substituteTyp (X <: S) Y U = X <: Typ.substituteTyp S Y U := by simp [substituteTyp]
  @[simp] lemma substituteTyp_typ : substituteTyp (X ≔  T) Y U = X ≔  Typ.substituteTyp T Y U := by simp [substituteTyp]

  instance instScopedTyp : Scoped (Assoc i) (.tvar i) where
    instantiateRec := instantiateRecTyp
    substitute := substituteTyp

  def instantiateRecCap (a : Assoc i) (k : Index (.var i)) (D : Cap i) : Assoc i :=
    map (Typ.instantiateRecCap · k D) a

  @[simp] lemma instantiateRecCap_val : instantiateRecCap (x ⦂  T) k D = x ⦂  Typ.instantiateRecCap T k D := by simp [instantiateRecCap]
  @[simp] lemma instantiateRecCap_sub : instantiateRecCap (X <: S) k D = X <: Typ.instantiateRecCap S k D := by simp [instantiateRecCap]
  @[simp] lemma instantiateRecCap_typ : instantiateRecCap (X ≔  T) k D = X ≔  Typ.instantiateRecCap T k D := by simp [instantiateRecCap]

  def substituteCap (a : Assoc i) (x : Atom (.var i)) (D : Cap i) : Assoc i :=
    map (Typ.substituteCap · x D) a

  @[simp] lemma substituteCap_val : substituteCap (x ⦂  T) y D = x ⦂  Typ.substituteCap T y D := by simp [substituteCap]
  @[simp] lemma substituteCap_sub : substituteCap (X <: S) y D = X <: Typ.substituteCap S y D := by simp [substituteCap]
  @[simp] lemma substituteCap_typ : substituteCap (X ≔  T) y D = X ≔  Typ.substituteCap T y D := by simp [substituteCap]

  def instantiateRecVar (a : Assoc i) (k : Index (.var i)) (u : Var (.var i)) : Assoc i :=
    instantiateRecCap a k {u}

  @[simp] lemma instantiateRecVar_val : instantiateRecVar (x ⦂  T) k u = x ⦂  Typ.instantiateRecVar T k u := by simp [instantiateRecVar]
  @[simp] lemma instantiateRecVar_sub : instantiateRecVar (X <: S) k u = X <: Typ.instantiateRecVar S k u := by simp [instantiateRecVar]
  @[simp] lemma instantiateRecVar_typ : instantiateRecVar (X ≔  T) k u = X ≔  Typ.instantiateRecVar T k u := by simp [instantiateRecVar]

  def substituteVar (a : Assoc i) (x : Atom (.var i)) (u : Var (.var i)) : Assoc i :=
    substituteCap a x {u}

  @[simp] lemma substituteVar_val : substituteVar (x ⦂  T) y u = x ⦂  Typ.substituteVar T y u := by simp [substituteVar]
  @[simp] lemma substituteVar_sub : substituteVar (X <: S) y u = X <: Typ.substituteVar S y u := by simp [substituteVar]
  @[simp] lemma substituteVar_typ : substituteVar (X ≔  T) y u = X ≔  Typ.substituteVar T y u := by simp [substituteVar]

  instance instScopedVar : Scoped (Assoc i) (.var i) where
    instantiateRec := instantiateRecVar
    substitute := substituteVar

  @[aesop safe forward]
  lemma substituteTyp_fresh {X : Atom (.tvar i)} {a : Assoc i} {U : Typ i} :
    X ∉ fvTyp a →
    substituteTyp a X U = a
  := by
    cases a <;> simp
      <;> intros X.NotIn
      <;> apply Typ.substituteTyp_fresh (by clear * - X.NotIn; aesop)

  @[aesop safe forward]
  lemma WellScopedRec_instantiateRecTyp {n : ℕ} {a : Assoc i} {U : Typ i} :
    WellScopedRec n (instantiateRecTyp a n U) →
    WellScopedRec (n + 1) a
  := by cases a <;> exact Typ.WellScopedRec_instantiateRecTyp

  @[aesop safe forward]
  lemma instantiateRecTyp_WellScopedRec {K : Index (.tvar i)} {a : Assoc i} {U : Typ i} :
    WellScopedRec n a →
    K >= n →
    instantiateRecTyp a K U = a
  := by
    cases a <;> simp
      <;> rename_i x T
      <;> intros T.WS geq
      <;> apply Typ.instantiateRecTyp_WellScopedRec T.WS geq

  instance instScopedInfrastructureTyp : Scoped.Infrastructure (Assoc i) (.tvar i) where
    substitute_fresh := substituteTyp_fresh
    WellScopedRec_instantiateRec := WellScopedRec_instantiateRecTyp
    instantiateRec_WellScopedRec := instantiateRecTyp_WellScopedRec

  @[aesop safe forward]
  lemma substituteCap_fresh {x : Atom (.var i)} {a : Assoc i} {D : Cap i} :
    x ∉ fvVar a →
    substituteCap a x D = a
  := by
    cases a <;> simp
      <;> intros X.NotIn
      <;> apply Typ.substituteCap_fresh (by clear * - X.NotIn; aesop)

  @[aesop safe forward]
  lemma substituteVar_fresh {x : Atom (.var i)} {a : Assoc i} {u : Var (.var i)} :
    x ∉ fvVar a →
    substituteVar a x u = a
  := substituteCap_fresh

  @[aesop safe forward]
  lemma WellScopedRec_instantiateRecCap {n : ℕ} {a : Assoc i} {D : Cap i} :
    WellScopedRec n (instantiateRecCap a n D) →
    WellScopedness.WellScopedRec (n + 1) a
  := by cases a <;> exact Typ.WellScopedRec_instantiateRecCap

  @[aesop safe forward]
  lemma WellScopedRec_instantiateRecVar {n : ℕ} {a : Assoc i} {u : Var (.var i)} :
    WellScopedRec n (instantiateRecVar a n u) →
    WellScopedness.WellScopedRec (n + 1) a
  := WellScopedRec_instantiateRecCap

  @[aesop safe forward]
  lemma instantiateRecCap_WellScopedRec {k : Index (.var i)} {a : Assoc i} {D : Cap i} :
    WellScopedRec n a →
    k >= n →
    instantiateRecCap a k D = a
  := by
    cases a <;> simp
      <;> rename_i x T
      <;> intros T.WS geq
      <;> apply Typ.instantiateRecCap_WellScopedRec T.WS geq

  @[aesop safe forward]
  lemma instantiateRecVar_WellScopedRec {k : Index (.var i)} {a : Assoc i} {u : Var (.var i)} :
    WellScopedRec n a →
    k >= n →
    instantiateRecVar a k u = a
  := instantiateRecCap_WellScopedRec

  instance instScopedInfrastructureVar : Scoped.Infrastructure (Assoc i) (.var i) where
    substitute_fresh := substituteVar_fresh
    WellScopedRec_instantiateRec := WellScopedRec_instantiateRecVar
    instantiateRec_WellScopedRec := instantiateRecVar_WellScopedRec
end Assoc

namespace Env
  def fvTyp (Γ : Env i) : Finset (Atom (.tvar i)) :=
    Env.fold (init := ∅) (· ∪ Assoc.fvTyp ·) Γ

  @[simp] lemma fvTyp_nil : fvTyp (i := i) ∅ = ∅ := by rfl
  @[simp] lemma fvTyp_cons : fvTyp (Γ ▷ a) = fvTyp Γ ∪ Assoc.fvTyp a := by simp only [fvTyp,fold_cons_comm]

  def fvVar (Γ : Env i) : Finset (Atom (.var i)) :=
    Env.fold (init := ∅) (· ∪ Assoc.fvVar ·) Γ

  @[simp] lemma fvVar_nil : fvVar (i := i) ∅ = ∅ := by rfl
  @[simp] lemma fvVar_cons : fvVar (Γ ▷ a) = fvVar Γ ∪ Assoc.fvVar a := by simp only [fvVar,fold_cons_comm]

  instance instFreeVariablesTyp : FreeVariables (Env i) (.tvar i) where
    fv := fvTyp

  instance instFreeVariablesVar : FreeVariables (Env i) (.var i) where
    fv := fvVar

  @[simp]
  def WellScopedRec (n : Nat) (Γ : Env i) : Prop :=
    Env.Forall (Assoc.WellScopedRec n) Γ

  @[simp]
  def WellScoped (Γ : Env i) : Prop :=
    Env.Forall Assoc.WellScoped Γ

  namespace WellScoped
    lemma WellScopedRec0 :
      WellScoped Γ →
      WellScopedRec 0 Γ
    := Env.Forall.imp (@Assoc.WellScoped.WellScopedRec0 _)

    lemma weaken :
      m ≤ n →
      WellScopedRec m a →
      WellScopedRec n a
    := fun leq => Env.Forall.imp (fun _ WS => Assoc.WellScoped.weaken leq WS)

    instance instWellScopedness : WellScopedness (Env i) where
      WellScopedRec := WellScopedRec
      WellScoped := WellScoped

    instance instWellScopednessInfrastructure : WellScopedness.Infrastructure (Env i) where
      WellScopedRec0 := WellScopedRec0
      weaken := weaken
  end WellScoped

  def instantiateRecTyp (Γ : Env i) (K : Index (.tvar i)) (U : Typ i) : Env i :=
    map (Typ.instantiateRecTyp · K U) Γ

  @[simp] lemma instantiateRecTyp_nil : instantiateRecTyp ∅ K U = ∅ := by rfl
  @[simp] lemma instantiateRecTyp_cons : instantiateRecTyp (Γ ▷ a) K U = instantiateRecTyp Γ K U ▷ Assoc.instantiateRecTyp a K U := by rfl

  @[simp] lemma dom_instantiateRecTyp : dom (α := α) (instantiateRecTyp Γ K U) = dom Γ := by simp [instantiateRecTyp]
  @[simp] lemma mem_instantiateRecTyp_of_mem : a ∈ Γ → Assoc.instantiateRecTyp a K U ∈ instantiateRecTyp Γ K U := by simp [instantiateRecTyp,Assoc.instantiateRecTyp]; exact mem_map_of_mem
  @[simp] lemma mem_instantiateRecTyp : b ∈ instantiateRecTyp Γ K U ↔ ∃ a ∈ Γ, Assoc.instantiateRecTyp a K U = b := by simp [instantiateRecTyp,Assoc.instantiateRecTyp]; exact mem_map

  def substituteTyp (Γ : Env i) (X : Atom (.tvar i)) (U : Typ i) : Env i :=
    map (Typ.substituteTyp · X U) Γ

  @[simp] lemma substituteTyp_nil : substituteTyp ∅ X U = ∅ := by rfl
  @[simp] lemma substituteTyp_cons : substituteTyp (Γ ▷ a) X U = substituteTyp Γ X U ▷ Assoc.substituteTyp a X U := by rfl

  @[simp] lemma dom_substituteTyp : dom (α := α) (substituteTyp Γ X U) = dom Γ := by simp [substituteTyp]
  @[simp] lemma mem_substituteTyp_of_mem : a ∈ Γ → Assoc.substituteTyp a X U ∈ substituteTyp Γ X U := by simp [substituteTyp,Assoc.substituteTyp]; exact mem_map_of_mem
  @[simp] lemma mem_substituteTyp : b ∈ substituteTyp Γ X U ↔ ∃ a ∈ Γ, Assoc.substituteTyp a X U = b := by simp [substituteTyp,Assoc.substituteTyp]; exact mem_map

  instance instScopedTyp : Scoped (Env i) (.tvar i) where
    instantiateRec := instantiateRecTyp
    substitute := substituteTyp

  def instantiateRecCap (Γ : Env i) (k : Index (.var i)) (D : Cap i) : Env i :=
    map (Typ.instantiateRecCap · k D) Γ

  @[simp] lemma instantiateRecCap_nil : instantiateRecCap ∅ k D = ∅ := by rfl
  @[simp] lemma instantiateRecCap_cons : instantiateRecCap (Γ ▷ a) k D = instantiateRecCap Γ k D ▷ Assoc.instantiateRecCap a k D := by rfl

  @[simp] lemma dom_instantiateRecCap : dom (α := α) (instantiateRecCap Γ k D) = dom Γ := by simp [instantiateRecCap]
  @[simp] lemma mem_instantiateRecCap_of_mem : a ∈ Γ → Assoc.instantiateRecCap a k D ∈ instantiateRecCap Γ k D := by simp [instantiateRecCap,Assoc.instantiateRecCap]; exact mem_map_of_mem
  @[simp] lemma mem_instantiateRecCap : b ∈ instantiateRecCap Γ k D ↔ ∃ a ∈ Γ, Assoc.instantiateRecCap a k D = b := by simp [instantiateRecCap,Assoc.instantiateRecCap]; exact mem_map

  def substituteCap (Γ : Env i) (x : Atom (.var i)) (D : Cap i) : Env i :=
    map (Typ.substituteCap · x D) Γ

  @[simp] lemma substituteCap_nil : substituteCap ∅ x D = ∅ := by rfl
  @[simp] lemma substituteCap_cons : substituteCap (Γ ▷ a) x D = substituteCap Γ x D ▷ Assoc.substituteCap a x D := by rfl

  @[simp] lemma dom_substituteCap : dom (α := α) (substituteCap Γ x u) = dom Γ := by simp [substituteCap]
  @[simp] lemma mem_substituteCap_of_mem : a ∈ Γ → Assoc.substituteCap a x u ∈ substituteCap Γ x u := by simp [substituteCap,Assoc.substituteCap]; exact mem_map_of_mem
  @[simp] lemma mem_substituteCap : b ∈ substituteCap Γ x u ↔ ∃ a ∈ Γ, Assoc.substituteCap a x u = b := by simp [substituteCap,Assoc.substituteCap]; exact mem_map


  def instantiateRecVar (Γ : Env i) (k : Index (.var i)) (u : Var (.var i)) : Env i :=
    instantiateRecCap Γ k {u}

  @[simp] lemma instantiateRecVar_nil : instantiateRecVar ∅ k u = ∅ := by rfl
  @[simp] lemma instantiateRecVar_cons : instantiateRecVar (Γ ▷ a) k u = instantiateRecVar Γ k u ▷ Assoc.instantiateRecVar a k u := by rfl

  @[simp] lemma dom_instantiateRecVar : dom (α := α) (instantiateRecVar Γ k u) = dom Γ := by simp only [instantiateRecVar]; exact dom_instantiateRecCap
  @[simp] lemma mem_instantiateRecVar_of_mem : a ∈ Γ → Assoc.instantiateRecVar a k u ∈ instantiateRecVar Γ k u :=  by simp only [instantiateRecVar]; exact mem_instantiateRecCap_of_mem
  @[simp] lemma mem_instantiateRecVar : b ∈ instantiateRecVar Γ k u ↔ ∃ a ∈ Γ, Assoc.instantiateRecVar a k u = b := by simp only [instantiateRecVar]; exact mem_instantiateRecCap

  def substituteVar (Γ : Env i) (x : Atom (.var i)) (u : Var (.var i)) : Env i :=
    substituteCap Γ x {u}

  @[simp] lemma substituteVar_nil : substituteVar ∅ x u = ∅ := by rfl
  @[simp] lemma substituteVar_cons : substituteVar (Γ ▷ a) x u = substituteVar Γ x u ▷ Assoc.substituteVar a x u := by rfl

  @[simp] lemma dom_substituteVar : dom (α := α) (substituteVar Γ x u) = dom Γ := by simp only [substituteVar]; exact dom_substituteCap
  @[simp] lemma mem_substituteVar_of_mem : a ∈ Γ → Assoc.substituteVar a x u ∈ substituteVar Γ x u := by simp only [substituteVar]; exact mem_substituteCap_of_mem
  @[simp] lemma mem_substituteVar : b ∈ substituteVar Γ x u ↔ ∃ a ∈ Γ, Assoc.substituteVar a x u = b := by simp only [substituteVar]; exact mem_substituteCap

  instance instScopedVar : Scoped (Env i) (.var i) where
    instantiateRec := instantiateRecVar
    substitute := substituteVar

  @[aesop safe forward]
  lemma substituteTyp_fresh {X : Atom (.tvar i)} {Γ : Env i} {U : Typ i} :
    X ∉ fvTyp Γ →
    substituteTyp Γ X U = Γ
  := by
    intros X.NotIn
    induction Γ <;> simp at *
    case cons Γ a IH =>
    exact ⟨IH (X.NotIn ∘ Or.inl), Assoc.substituteTyp_fresh (X.NotIn ∘ Or.inr)⟩

  @[aesop safe forward]
  lemma WellScopedRec_instantiateRecTyp {n : ℕ} {Γ : Env i} {U : Typ i} :
    WellScopedRec n (instantiateRecTyp Γ n U) →
    WellScopedRec (n + 1) Γ
  := by
    intros WS
    simp at WS
    induction Γ <;> simp at *
    case cons Γ a IH =>
    exact ⟨IH WS.1, Assoc.WellScopedRec_instantiateRecTyp WS.2⟩

  @[aesop safe forward]
  lemma instantiateRecTyp_WellScopedRec {K : Index (.tvar i)} {Γ : Env i} {U : Typ i} :
    WellScopedRec n Γ →
    K >= n →
    instantiateRecTyp Γ K U = Γ
  := by
    intros WS geq
    simp at WS
    induction Γ <;> simp at *
    case cons Γ a IH =>
    exact ⟨IH WS.1, Assoc.instantiateRecTyp_WellScopedRec WS.2 geq⟩

  instance instScopedInfrastructureTyp : Scoped.Infrastructure (Env i) (.tvar i) where
    substitute_fresh := substituteTyp_fresh
    WellScopedRec_instantiateRec := WellScopedRec_instantiateRecTyp
    instantiateRec_WellScopedRec := instantiateRecTyp_WellScopedRec

  @[aesop safe forward]
  lemma substituteCap_fresh {x : Atom (.var i)} {Γ : Env i} {D : Cap i} :
    x ∉ fvVar Γ →
    substituteCap Γ x D = Γ
  := by
    intros x.NotIn
    induction Γ <;> simp at *
    case cons Γ a IH =>
    exact ⟨IH (x.NotIn ∘ Or.inl), Assoc.substituteCap_fresh (x.NotIn ∘ Or.inr)⟩

  @[aesop safe forward]
  lemma substituteVar_fresh {x : Atom (.var i)} {Γ : Env i} {u : Var (.var i)} :
    x ∉ fvVar Γ →
    substituteVar Γ x u = Γ
  := substituteCap_fresh

  @[aesop safe forward]
  lemma WellScopedRec_instantiateRecCap {n : ℕ} {Γ : Env i} {D : Cap i} :
    WellScopedRec n (instantiateRecCap Γ n D) →
    WellScopedRec (n + 1) Γ
  := by
    intros WS
    simp at WS
    induction Γ <;> simp at *
    case cons Γ a IH =>
    exact ⟨IH WS.1, Assoc.WellScopedRec_instantiateRecCap WS.2⟩

  @[aesop safe forward]
  lemma WellScopedRec_instantiateRecVar {n : ℕ} {Γ : Env i} {u : Var (.var i)} :
    WellScopedRec n (instantiateRecVar Γ n u) →
    WellScopedRec (n + 1) Γ
  := WellScopedRec_instantiateRecCap

  @[aesop safe forward]
  lemma instantiateRecCap_WellScopedRec {k : Index (.var i)} {Γ : Env i} {D : Cap i} :
    WellScopedRec n Γ →
    k >= n →
    instantiateRecCap Γ k D = Γ
  := by
    intros WS geq
    simp at WS
    induction Γ <;> simp at *
    case cons Γ a IH =>
    exact ⟨IH WS.1, Assoc.instantiateRecCap_WellScopedRec WS.2 geq⟩

  @[aesop safe forward]
  lemma instantiateRecVar_WellScopedRec {k : Index (.var i)} {Γ : Env i} {u : Var (.var i)} :
    WellScopedRec n Γ →
    k >= n →
    instantiateRecVar Γ k u = Γ
  := instantiateRecCap_WellScopedRec

  instance instScopedInfrastructureVar : Scoped.Infrastructure (Env i) (.var i) where
    substitute_fresh := substituteVar_fresh
    WellScopedRec_instantiateRec := WellScopedRec_instantiateRecVar
    instantiateRec_WellScopedRec := instantiateRecVar_WellScopedRec
end Env
