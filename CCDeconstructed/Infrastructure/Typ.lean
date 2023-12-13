import CCDeconstructed.Syntax
import CCDeconstructed.Classes
import CCDeconstructed.Tactics
import CCDeconstructed.Infrastructure.Var
import CCDeconstructed.Infrastructure.Cap

set_option linter.unusedVariables false

open Scoped FreeVariables VarCat

namespace Typ
  instance : Coe (Var (.tvar i)) (Typ i) where
    coe := Typ.var

  @[simp]
  def fvTyp (T : Typ i) : Finset (Atom (.tvar i)) :=
    match T with
    | .top => ∅
    | .var V => fv V
    | .arr A B => A.fvTyp ∪ B.fvTyp
    | .all _ A B => A.fvTyp ∪ B.fvTyp
    | @Typ.box _ _ A => A.fvTyp
    | .cap S _ => S.fvTyp

  @[simp]
  def fvVar (T : Typ i) : Finset (Atom (.var i)) :=
    match T with
    | .top => ∅
    | .var _ => ∅
    | .arr A B => A.fvVar ∪ B.fvVar
    | .all _ A B => A.fvVar ∪ B.fvVar
    | @Typ.box _ _ A => A.fvVar
    | .cap S C => S.fvVar ∪ fv C

  instance instFreeVariablesVar : FreeVariables (Typ i) (.var i) where
    fv := fvVar

  instance instFreeVariablesTVar : FreeVariables (Typ i) (.tvar i) where
    fv := fvTyp

  @[simp]
  def instantiateRecTyp (T : Typ i) (K : Index (tvar i)) (U : Typ i) : Typ i :=
    match T with
    | .top => .top
    | .var V => V.subst K U
    | .arr A B => .arr (A.instantiateRecTyp K U) (B.instantiateRecTyp (K + 1) U)
    | .all k A B => .all k (A.instantiateRecTyp K U) (B.instantiateRecTyp (K + 1) U)
    | Typ.box A => .box (A.instantiateRecTyp K U)
    | .cap S C => .cap (S.instantiateRecTyp K U) C

  @[simp]
  def substituteTyp (T : Typ i) (X : Atom (.tvar i)) (U : Typ i) : Typ i :=
    match T with
    | .top => .top
    | .var V => V.subst X U
    | .arr A B => .arr (A.substituteTyp X U) (B.substituteTyp X U)
    | .all k A B => .all k (A.substituteTyp X U) (B.substituteTyp X U)
    | @Typ.box _ _ A => .box (A.substituteTyp X U)
    | .cap S C => .cap (S.substituteTyp X U) C

  @[simp]
  def instantiateRecCap (T : Typ i) (k : Index (.var i)) (D : Cap i) : Typ i :=
    match T with
    | .top => .top
    | .var V => V
    | .arr A B => .arr (A.instantiateRecCap k D) (B.instantiateRecCap (k + 1) D)
    | .all k' A B => .all k' (A.instantiateRecCap k D) (B.instantiateRecCap (k + 1) D)
    | Typ.box A => .box (A.instantiateRecCap k D)
    | .cap S C => .cap (S.instantiateRecCap k D) (C.instantiateRecCap k D)

  @[simp]
  def instantiateRecVar (T : Typ i) (k : Index (.var i)) (u : Var (.var i)) : Typ i :=
    instantiateRecCap T k {u}

  @[simp]
  lemma instantiateRecCap_singleton_instantiateRecVar :
    instantiateRecCap T k {u} = instantiateRecVar T k u
  := rfl

  @[simp]
  def substituteCap (T : Typ i) (x : Atom (.var i)) (D : Cap i) : Typ i :=
    match T with
    | .top => .top
    | .var V => V
    | .arr A B => .arr (A.substituteCap x D) (B.substituteCap x D)
    | .all k' A B => .all k' (A.substituteCap x D) (B.substituteCap x D)
    | @Typ.box _ _ A => .box (A.substituteCap x D)
    | .cap S C => .cap (S.substituteCap x D) (C.substituteCap x D)

  @[simp]
  def substituteVar (T : Typ i) (x : Atom (.var i)) (u : Var (.var i)) : Typ i :=
    substituteCap T x {u}

  @[simp]
  lemma substituteCap_singleton_substituteVar :
    substituteCap T x {u} = substituteVar T x u
  := rfl

  mutual
    @[aesop unsafe]
    inductive _root_.Typ.Type : Typ i → Prop where
      | shape {S : Typ i} :
          Typ.Shape S →
          Typ.Type S
      | cap {S : Typ i} {C : Cap i} :
          Shape S →
          Cap.WellScoped C →
          Typ.Type (.cap S C)

    @[aesop unsafe]
    inductive _root_.Typ.Shape : Typ i → Prop where
      | var {V : Var (.tvar i)} :
          Var.WellScoped (allowCap := false) V →
          Typ.Shape (.var V)
      | top :
          Shape top
      | arr {S : Typ i} {C : Cap i} {U : Typ i} (L : Finset (Atom (.var i))) :
          Typ.Shape S →
          Cap.WellScoped C →
          (∀ x ∉ L, Typ.Type (Typ.instantiateRecVar U 0 x)) →
          Typ.Shape (.arr (.cap S C) U)
      | all {k : TypevarKind i} {S : Typ i} {U : Typ i} (L : Finset (Atom (.tvar i))) :
          Typ.Shape S →
          (∀ X ∉ L, Typ.Type (Typ.instantiateRecTyp U 0 (.var (.free X)))) →
          Typ.Shape (.all k S U)
      | box [HasFeature i .box_type] :
          Typ.Type T →
          Typ.Shape (@Typ.box i _ T)
  end

  @[aesop unsafe [constructors 50%]]
  inductive WellScopedRec {i : CC} : Nat → Typ i → Prop :=
    | top :
        WellScopedRec n .top
    | var :
        Var.WellScopedRec (allowCap := false) n V →
        WellScopedRec n (.var V)
    | arr :
        WellScopedRec n A →
        WellScopedRec (n + 1) B →
        WellScopedRec n (.arr A B)
    | all :
        WellScopedRec n A →
        WellScopedRec (n + 1) B →
        WellScopedRec n (.all k A B)
    | box [HasFeature i .box_type] :
        WellScopedRec n T →
        WellScopedRec n (.box T)
    | cap :
        WellScopedRec n S →
        Cap.WellScopedRec n C →
        WellScopedRec n (.cap S C)

  @[simp]
  instance instScopedTyp : Scoped (Typ i) (.tvar i) where
    instantiateRec := instantiateRecTyp
    substitute := substituteTyp

  @[simp]
  instance instScopedVar : Scoped (Typ i) (.var i) where
    instantiateRec := instantiateRecVar
    substitute := substituteVar

  @[aesop norm]
  def WellScoped {i : CC} : Typ i → Prop :=
    _root_.Typ.Type

  @[aesop unsafe]
  lemma WellScopedRec_instantiateRecTyp :
    WellScopedRec n (instantiateRecTyp T n U) →
    WellScopedRec (n + 1) T
  := by
    generalize Eq : instantiateRecTyp T n U = T'
    intros T'.WS
    induction' T'.WS generalizing T
    · case top n =>
      cases T <;> simp only [instantiateRecTyp] at Eq <;> constructor
      aesop
    · case var n V V.WS =>
      cases T <;> simp only [instantiateRecTyp] at Eq; constructor
      simp [Var.subst] at Eq
      split at Eq
      · case inl Eq.var =>
        cases Eq.var
        constructor
      · case inr Neq.var =>
        cases Eq
        apply Var.WellScoped.weaken (m := n) <;> aesop
    · case arr =>
      cases T <;> simp only [instantiateRecTyp] at Eq <;> constructor <;> aesop
    · case all =>
      cases T <;> simp only [instantiateRecTyp] at Eq <;> constructor <;> aesop
    · case box =>
      cases T <;> simp only [instantiateRecTyp] at Eq <;> constructor <;> aesop
    · case cap n S C S.WS C.WS S.IH =>
      cases T <;> simp only [instantiateRecTyp] at Eq <;> constructor
      · case var.a V =>
        cases V <;> simp at Eq
        case bound K =>
        split at Eq
        · case inl Eq.idx =>
          cases Eq.idx
          constructor
        · case inr Neq.idx =>
          simp at Eq
      · case cap.a S' C' =>
        injection Eq with Eq.S Eq.C
        apply S.IH Eq.S
      · injection Eq with Eq.S Eq.C
        cases Eq.C
        apply Cap.WellScoped.weaken (m := n) (by linarith) C.WS

  @[aesop unsafe]
  lemma WellScopedRec_instantiateRecCap :
    WellScopedRec n (instantiateRecCap T n D) →
    WellScopedRec (n + 1) T
  := by
    intros T.WS
    generalize Eq : instantiateRecCap T n D = T'
    rw [Eq] at T.WS
    induction' T.WS generalizing T
    · case top n =>
      cases T <;> simp only [instantiateRecCap] at Eq; constructor
    · case var n V V.WS =>
      cases T <;> simp only [instantiateRecCap] at Eq; constructor
      apply Var.WellScoped.weaken (m := n) <;> aesop
    · case arr =>
      cases T <;> simp only [instantiateRecCap] at Eq; constructor <;> aesop
    · case all =>
      cases T <;> simp only [instantiateRecCap] at Eq; constructor <;> aesop
    · case box =>
      cases T <;> simp only [instantiateRecCap] at Eq; constructor; aesop
    · case cap n S C S.WS C.WS S.IH =>
      cases T <;> simp only [instantiateRecCap] at Eq
      rename_i S' C'
      injection Eq with Eq.S Eq.C
      constructor
      · apply S.IH; aesop
      · apply Cap.WellScopedRec_instantiateRecCap (D := D)
        rw [Eq.C]
        exact C.WS

  @[aesop unsafe]
  lemma WellScopedRec_instantiateRecVar :
    WellScopedRec n (instantiateRecVar T n u) →
    WellScopedRec (n + 1) T
  := WellScopedRec_instantiateRecCap

  namespace WellScoped
    @[aesop unsafe]
    lemma WellScopedRec0 {T : Typ i} :
      WellScoped T →
      WellScopedRec 0 T
    := by
      revert T
      simp [WellScoped]
      apply Typ.Type.rec
        (motive_1 := fun {T : Typ i} (TType : _root_.Typ.Type T) => WellScopedRec 0 T)
        (motive_2 := fun {S : Typ i} (SShape : Shape S) => WellScopedRec 0 S)
      all_goals aesop

    @[aesop unsafe]
    lemma weaken :
      m <= n →
      WellScopedRec m T →
      WellScopedRec n T
    := by
      intros leq WS
      induction' WS generalizing n
      · case top =>
        constructor
      · case var m V V.WS =>
        constructor
        exact Var.WellScoped.weaken (m := m) leq V.WS
      · case arr m T U T.WS U.WS T.IH U.IH =>
        constructor
        · exact T.IH leq
        · exact U.IH (by linarith)
      · case all m S U k S.WS U.WS S.IH U.IH =>
        constructor
        · exact S.IH leq
        · exact U.IH (by linarith)
      · case box m T _ T.WS T.IH =>
        constructor
        exact T.IH leq
      · case cap m S C S.WS C.WS S.IH =>
        constructor
        · exact S.IH leq
        · exact Cap.WellScoped.weaken (m := m) leq C.WS

    instance instWellScopedness.Infrastructure : WellScopedness.Infrastructure (Typ i) where
      WellScopedRec := WellScopedRec
      WellScoped := WellScoped
      WellScopedRec0 := WellScopedRec0
      weaken := weaken
  end WellScoped

  @[aesop unsafe]
  lemma substituteTyp_fresh {X : Atom (.tvar i)} {T : Typ i} {U : Typ i} :
    X ∉ fvTyp T →
    substituteTyp T X U = T
  := by induction T <;> aesop

  @[aesop unsafe]
  lemma substituteTyp_instantiateRecTyp_intro :
    X ∉ fvTyp T →
    instantiateRecTyp T K U = substituteTyp (instantiateRecTyp T K X) X U
  := by
    intros X.NotIn
    induction T generalizing K <;> simp [fvTyp] at X.NotIn <;> simp [instantiateRecTyp,substituteTyp]
    · case var V =>
      split <;> simp [substituteTyp]
      case inr V.NotBound =>
      cases V
      · case free Y =>
        simp [Var.fv] at X.NotIn
        replace X.NotIn : Y ≠ X := X.NotIn ∘ Eq.symm
        simp [X.NotIn]
      · case bound K' =>
        simp at *
      · case cap Eq.cat =>
        cases Eq.cat
    · case arr T U T.IH U.IH =>
      apply And.intro
      · exact T.IH (X.NotIn ∘ Or.inl)
      · exact U.IH (X.NotIn ∘ Or.inr)
    · case all S U S.IH U.IH =>
      apply And.intro
      · exact S.IH (X.NotIn ∘ Or.inl)
      · exact U.IH (X.NotIn ∘ Or.inr)
    · case box T T.IH =>
      exact T.IH X.NotIn
    · case cap S C S.IH =>
      exact S.IH X.NotIn

  @[aesop unsafe]
  lemma substituteCap_instantiateRecCap_intro :
    x ∉ fv T →
    instantiateRecCap T k D = substituteCap (instantiateRecCap T k {.free x}) x D
  := by
    intros x.NotIn
    induction T generalizing k <;> simp [fv,fvVar] at x.NotIn <;> simp [instantiateRecCap,substituteCap]
    · case arr T U T.IH U.IH =>
      apply And.intro
      · exact T.IH (x.NotIn ∘ Or.inl)
      · exact U.IH (x.NotIn ∘ Or.inr)
    · case all S U S.IH U.IH =>
      apply And.intro
      · exact S.IH (x.NotIn ∘ Or.inl)
      · exact U.IH (x.NotIn ∘ Or.inr)
    · case box T T.IH =>
      apply T.IH x.NotIn
    · case cap S C S.IH =>
      apply And.intro
      · exact S.IH (x.NotIn ∘ Or.inl)
      · exact Cap.substituteCap_instantiateRecCap_intro (x.NotIn ∘ Or.inr)

  @[aesop unsafe]
  lemma substituteVar_instantiateRecVar_intro :
    x ∉ fvVar T →
    instantiateRecVar T k u = substituteVar (instantiateRecVar T k x) x u
  := substituteCap_instantiateRecCap_intro

  @[aesop unsafe]
  lemma instantiateRecTyp_WellScopedRec :
    WellScopedRec n T →
    K >= n →
    instantiateRecTyp T K U = T
  := by
    intros WS geq
    induction WS generalizing K <;> simp [instantiateRecTyp]
    · case var n V V.WS =>
      intros V.Bound
      cases V.Bound
      simp [Var.WellScopedRec] at V.WS
      exfalso
      simp [Index] at *
      linarith
    all_goals aesop

  @[aesop unsafe]
  lemma instantiateRecTyp_WellScoped :
    WellScoped T →
    instantiateRecTyp T K U = T
  := by
    intros WS
    apply instantiateRecTyp_WellScopedRec (WellScoped.WellScopedRec0 WS)
    linarith

  instance instScopedInfrastructureTyp : Scoped.Infrastructure (Typ i) (tvar i) where
    substitute_fresh := substituteTyp_fresh
    instantiateRec_WellScopedRec := instantiateRecTyp_WellScopedRec
    WellScopedRec_instantiateRec := WellScopedRec_instantiateRecTyp

  @[aesop unsafe]
  lemma substituteCap_fresh :
    x ∉ fvVar T →
    substituteCap T x D = T
  := by
    intros x.NotIn
    induction T <;> simp [substituteCap]
    · case arr T U T.IH U.IH =>
      apply And.intro <;> aesop
    · case all S U S.IH U.IH =>
      apply And.intro <;> aesop
    · case box T T.IH =>
      apply T.IH x.NotIn
    · case cap S C S.IH =>
      apply And.intro
      · aesop
      · apply Cap.substituteCap_fresh
        aesop

  @[aesop unsafe]
  lemma substituteVar_fresh :
    x ∉ fvVar T →
    substituteVar T x u = T
  := substituteCap_fresh

  @[aesop unsafe]
  lemma instantiateRecCap_WellScopedRec :
    WellScopedRec n T →
    k >= n →
    instantiateRecCap T k D = T
  := by
    intros WS geq
    induction WS generalizing k <;> simp only [instantiateRecCap]
    · case arr => aesop
    · case all => aesop
    · case box => aesop
    · case cap n S C S.WS C.WS S.IH =>
      simp [-Cap.instantiateRecCap]
      exact ⟨S.IH geq, Cap.instantiateRecCap_WellScopedRec C.WS geq⟩

  @[aesop unsafe]
  lemma instantiateRecVar_WellScopedRec :
    WellScopedRec n T →
    k >= n →
    instantiateRecCap T k u = T
  := instantiateRecCap_WellScopedRec

  @[aesop unsafe]
  lemma instantiateRecCap_WellScoped :
    WellScoped T →
    instantiateRecCap T k D = T
  := by
    intros WS
    apply instantiateRecCap_WellScopedRec (WellScoped.WellScopedRec0 WS)
    linarith

  @[aesop unsafe]
  lemma instantiateRecVar_WellScoped :
    WellScoped T →
    instantiateRecVar T k u = T
  := instantiateRecCap_WellScoped

  instance instScopedInfrastructureVar : Scoped.Infrastructure (Typ i) (.var i) where
    instantiateRec := instantiateRecVar
    substitute := substituteVar
    substitute_fresh := substituteVar_fresh
    WellScopedRec_instantiateRec := WellScopedRec_instantiateRecVar
    instantiateRec_WellScopedRec := instantiateRecVar_WellScopedRec

  @[aesop unsafe]
  lemma fvVar_subset_fvVar_instantiateRecCap :
    fvVar T ⊆ fvVar (instantiateRecCap T k D)
  := by
    induction T generalizing k <;> simp [fvVar]
    · case arr T U T.IH U.IH =>
      apply Finset.union_subset_union T.IH U.IH
    · case all S U S.IH U.IH =>
      apply Finset.union_subset_union S.IH U.IH
    · case box _ T T.IH =>
      exact T.IH
    · case cap S C S.IH =>
      exact Finset.union_subset_union S.IH Cap.fv_subset_fv_instantiateRecCap

  @[aesop unsafe]
  lemma fvVar_subset_fvVar_instantiateRecVar :
    fvVar T ⊆ fvVar (instantiateRecVar T k u)
  := fvVar_subset_fvVar_instantiateRecCap

  @[aesop unsafe]
  lemma fvVar_subset_fvVar_instantiateRecTyp :
    fvVar T ⊆ fvVar (instantiateRecTyp T k U)
  := by
    induction T generalizing k <;> simp [fvVar]
    · case arr T U T.IH U.IH =>
      apply Finset.union_subset_union T.IH U.IH
    · case all S U S.IH U.IH =>
      apply Finset.union_subset_union S.IH U.IH
    · case box _ T T.IH =>
      exact T.IH
    · case cap S C S.IH =>
      exact Finset.union_subset_union_left S.IH

  @[aesop unsafe]
  lemma fvTyp_subset_fvTyp_instantiateRecCap :
    fvTyp T ⊆ fvTyp (instantiateRecCap T k U)
  := by
    induction T generalizing k <;> simp [fvTyp]
    · case arr T U T.IH U.IH =>
      apply Finset.union_subset_union T.IH U.IH
    · case all S U S.IH U.IH =>
      apply Finset.union_subset_union S.IH U.IH
    · case box _ T T.IH =>
      exact T.IH
    · case cap S C S.IH =>
      exact S.IH

  @[aesop unsafe]
  lemma fvTyp_subset_fvTyp_instantiateRecVar :
    fvTyp T ⊆ fvTyp (instantiateRecVar T k u)
  := fvTyp_subset_fvTyp_instantiateRecCap

  @[aesop unsafe]
  lemma fvTyp_subset_fvTyp_instantiateRecTyp :
    fvTyp T ⊆ fvTyp (instantiateRecTyp T k U)
  := by
    induction T generalizing k <;> simp [fvTyp]
    · case var V =>
      cases V <;> simp [instantiateRecTyp,Var.fv,fvTyp]
    · case arr T U T.IH U.IH =>
      apply Finset.union_subset_union T.IH U.IH
    · case all S U S.IH U.IH =>
      apply Finset.union_subset_union S.IH U.IH
    · case box _ T T.IH =>
      exact T.IH
    · case cap S C S.IH =>
      exact S.IH

  @[aesop unsafe]
  lemma substituteTyp_instantiateRecTyp {X : Atom (.tvar i)} {U₁ : Typ i} {T : Typ i} {K : Index (.tvar i)}  {U₂ : Typ i} :
    WellScoped U₂ →
    substituteTyp (instantiateRecTyp T K U₁) X U₂ = instantiateRecTyp (substituteTyp T X U₂) K (substituteTyp U₁ X U₂)
  := by
    intros U₂.WS
    induction T generalizing K <;> simp [instantiateRecTyp,substituteTyp]
    · case var V =>
      split
      · case inl Eq.Bound =>
        have Neq.Free : V ≠ Var.free X := by
          simp [Eq.Bound]
        simp [instantiateRecTyp,Eq.Bound,Neq.Free]
      · case inr Neq.Bound =>
        split
        · case inl Eq.Free =>
          simp [substituteTyp,Eq.Free]
          symm
          apply instantiateRecTyp_WellScoped U₂.WS
        · case inr Neq.Free =>
          simp [substituteTyp,instantiateRecTyp,Neq.Bound,Neq.Free]
    all_goals aesop

  @[aesop unsafe]
  lemma substituteCap_instantiateRecCap {x : Atom (.var i)} {D₁ : Cap i} {T : Typ i} {k : Index (.var i)}  {D₂ : Cap i} :
    Cap.WellScoped D₂ →
    substituteCap (instantiateRecCap T k D₁) x D₂ = instantiateRecCap (substituteCap T x D₂) k (Cap.substituteCap D₁ x D₂)
  := by
    intros D₂.WS
    induction T generalizing k <;> simp [instantiateRecCap,substituteCap]
    · case arr S T S.IH T.IH =>
      exact ⟨S.IH, T.IH⟩
    · case all S T S.IH T.IH =>
      exact ⟨S.IH, T.IH⟩
    · case box T T.IH =>
      exact T.IH
    · case cap S C S.IH =>
      apply And.intro S.IH
      apply Cap.substituteCap_instantiateRecCap D₂.WS

  lemma substituteVar_instantiateRecVar {x : Atom (.var i)} {u₁ : Var (.var i)} {T : Typ i} {k : Index (.var i)}  {u₂ : Var (.var i)} :
    Var.WellScoped (allowCap := allowCap) u₂ →
    substituteVar (instantiateRecVar T k u₁) x u₂ = instantiateRecVar (substituteVar T x u₂) k (Var.substitute u₁ x u₂)
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
    simp [Cap.WellScoped]
    exact Var.WellScoped.map_allowCap (by simp) u₂.WS

  @[aesop unsafe]
  lemma substituteTyp_instantiateRecCap {X : Atom (.tvar i)} {U : Typ i} {T : Typ i} {k : Index (.var i)}  {D : Cap i} :
    WellScoped U →
    substituteTyp (instantiateRecCap T k D) X U = instantiateRecCap (substituteTyp T X U) k D
  := by
    intros U.WS
    induction T generalizing k <;> simp [instantiateRecCap,substituteTyp]
    · case var V =>
      split
      · case inl Eq =>
        cases Eq
        symm
        apply Typ.instantiateRecCap_WellScoped U.WS
      · case inr Neq =>
        simp [instantiateRecCap]
    all_goals aesop

  @[aesop unsafe]
  lemma substituteTyp_instantiateRecVar {X : Atom (.tvar i)} {U : Typ i} {T : Typ i} {k : Index (.var i)}  {u : Var (.var i)} :
    WellScoped U →
    substituteTyp (instantiateRecVar T k u) X U = instantiateRecVar (substituteTyp T X U) k u
  := substituteTyp_instantiateRecCap

  @[aesop unsafe]
  lemma substituteCap_instantiateRecTyp {x : Atom (.var i)} {U : Typ i} {T : Typ i} {K : Index (.tvar i)}  {D : Cap i} :
    substituteCap (instantiateRecTyp T K U) x D = instantiateRecTyp (substituteCap T x D) K (substituteCap U x D)
  := by
    induction T generalizing K <;> aesop

  @[aesop unsafe]
  lemma substituteVar_instantiateRecTyp {x : Atom (.var i)} {U : Typ i} {T : Typ i} {K : Index (.tvar i)}  {u : Var (.var i)} :
    substituteVar (instantiateRecTyp T K U) x u = instantiateRecTyp (substituteVar T x u) K (substituteVar U x u)
  := substituteCap_instantiateRecTyp

  @[aesop unsafe]
  lemma Shape_substituteTyp {S : Typ i} {X : Atom (.tvar i)} {U : Typ i} :
    Typ.Shape U →
    Typ.Shape S →
    Typ.Shape (substituteTyp S X U)
  := by
    intros U.Shape
    revert S
    apply Typ.Shape.rec
      (motive_1 := fun (T : Typ i) (TType : Typ.Type T) => Typ.Type (substituteTyp T X U))
      (motive_2 := fun (S : Typ i) (SShape : Typ.Shape S) => Typ.Shape (substituteTyp S X U))
    · case shape =>
      intros S S.Shape SXU.Shape
      exact Typ.Type.shape SXU.Shape
    · case cap =>
      intros S C S.Shape C.WS SXU.Shape
      simp [substituteTyp]
      apply Typ.Type.cap SXU.Shape C.WS
    · case var =>
      intros Y
      simp [substituteTyp]
      split
      · case inl Eq =>
        cases Eq
        simp [Var.WellScoped]
        exact U.Shape
      · case inr Neq =>
        apply Typ.Shape.var
    · case top =>
      simp [substituteTyp]
      exact Typ.Shape.top
    · case arr =>
      intros S C T L S.Shape C.WS T.WS SXU.Shape T.IH
      simp [substituteTyp]
      apply Typ.Shape.arr L SXU.Shape C.WS
      intros x x.Fresh
      rw [<- substituteTyp_instantiateRecVar (Typ.Type.shape U.Shape)]
      apply T.IH x x.Fresh
    · intros k S T L S.Shape S.WS T.WF T.IH
      simp [substituteTyp]
      apply Typ.Shape.all (L ∪ {X}) T.WF
      intros Y Y.Fresh
      rw [<- substituteTyp_fresh (T := Typ.var (Var.free Y)) (X := X) (U := U)]
      · rw [<- substituteTyp_instantiateRecTyp (Typ.Type.shape U.Shape)]
        apply T.IH Y (by aesop)
      · simp [fvTyp,Var.fv]
        aesop
    · case box =>
      intros T _ T.Type TXU.Type
      simp [substituteTyp]
      apply Typ.Shape.box TXU.Type

  @[aesop unsafe]
  lemma Shape_substituteCap {S : Typ i} {x : Atom (.var i)} {D : Cap i} :
    Cap.WellScoped D →
    Typ.Shape S →
    Typ.Shape (substituteCap S x D)
  := by
    intros D.WS
    revert S
    apply Typ.Shape.rec
      (motive_1 := fun (T : Typ i) (TType : Typ.Type T) => Typ.Type (substituteCap T x D))
      (motive_2 := fun (S : Typ i) (SShape : Typ.Shape S) => Typ.Shape (substituteCap S x D))
    · case shape =>
      intros S S.Shape SxD.Shape
      exact Typ.Type.shape SxD.Shape
    · case cap =>
      intros S C S.Shape C.WS SxD.Shape
      simp [substituteCap]
      exact Typ.Type.cap SxD.Shape (Cap.WellScoped_substituteCap D.WS C.WS)
    · case var =>
      intros V V.WS
      simp [substituteCap]
      exact Typ.Shape.var V.WS
    · case top =>
      simp [substituteCap]
      exact Typ.Shape.top
    · case arr =>
      intros S C T L S.Shape C.WS T.WS SxD.Shape T.IH
      simp [substituteCap]
      apply Typ.Shape.arr (L ∪ {x}) SxD.Shape (Cap.WellScoped_substituteCap D.WS C.WS)
      unfold instantiateRecVar
      intros y y.Fresh
      conv in {.free y} =>
        rw [<- Cap.substituteCap_fresh (C := {.free y}) (x := x) (D := D) (by simp [Cap.fv,Var.fv]; aesop)]
        rfl
      rw [<- substituteCap_instantiateRecCap D.WS]
      apply T.IH y (by clear * - y.Fresh; aesop)
    · case all =>
      intros k S T L S.Shape S.WS T.WF T.IH
      simp [substituteCap]
      apply Typ.Shape.all L T.WF
      intros Y Y.Fresh
      conv in Typ.var (Var.free Y) =>
        rw [<- substituteCap_fresh (T := Typ.var (Var.free Y)) (x := x) (D := D) (by simp [fvVar])]
        rfl
      rw [<- substituteCap_instantiateRecTyp (x := x) (D := D)]
      exact T.IH Y Y.Fresh
    · case box =>
      intros T _ T.Type TXU.Type
      simp [substituteCap]
      exact Typ.Shape.box TXU.Type

  @[aesop unsafe]
  lemma Shape_substituteVar {S : Typ i} {x : Atom (.var i)} {u : Var (.var i)} :
    Var.WellScoped (allowCap := allowCap) u →
    Typ.Shape S →
    Typ.Shape (substituteVar S x u)
  := by
    intros u.WS S.Shape
    apply Shape_substituteCap
    · simp [Cap.WellScoped]
      exact Var.WellScoped.map_allowCap (by simp) u.WS
    · exact S.Shape

  def dcs : Typ i → Cap i
    | .cap S C => Typ.dcs S ∪ C
    | .arr _ U => Typ.dcs U
    | .all _ _ U => Typ.dcs U
    | @Typ.box _ _ T => Typ.dcs T
    | _ => ∅
end Typ
