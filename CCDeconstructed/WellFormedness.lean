import CCDeconstructed.Var
import CCDeconstructed.Syntax
import CCDeconstructed.CC
import CCDeconstructed.Infrastructure

open Feature VarCat Env

set_option linter.unusedVariables false

@[aesop norm]
def Var.WellFormed {i : CC} {α : VarCat i} {allowCap : Bool} (Γ : Env i) : Var α → Prop
  | .free x => x ∈ dom Γ
  | .bound _ => False
  | .cap => if allowCap then True else False

namespace Var.WellFormed
  @[aesop safe]
  def map_allowCap {i : CC} {α : VarCat i} {allowCap₁ allowCap₂ : Bool} {Γ : Env i} {v : Var α} :
    allowCap₁ ≤ allowCap₂ →
    Var.WellFormed (allowCap := allowCap₁) Γ v →
    Var.WellFormed (allowCap := allowCap₂) Γ v
  := by
    cases v
      <;> cases allowCap₁
      <;> cases allowCap₂
      <;> simp [Bool.instLEBool,Var.WellFormed]

  @[aesop safe]
  lemma toWellScoped {α : VarCat i} {allowCap : Bool} {Γ : Env i} {v : Var α} :
    WellFormed (allowCap := allowCap) Γ v →
    WellScoped (allowCap := allowCap) v
  := by cases v <;> simp [WellFormed,Var.WellScoped]

  @[aesop unsafe 40%]
  lemma weaken {α : VarCat i} {allowCap : Bool} {Γ Θ Δ : Env i} {v : Var α} :
    WellFormed (allowCap := allowCap) (Γ ++ Δ) v →
    Env.Nodup (Γ ++ Θ ++ Δ) →
    WellFormed (allowCap := allowCap) (Γ ++ Θ ++ Δ) v
  := by
    simp only [WellFormed,Env.dom_concat]
    cases v <;> simp only [WellFormed,Env.dom_concat] <;> aesop

  @[aesop unsafe]
  lemma ignore_bindings {Γ Δ : Env i} {α β : VarCat i} {x : Atom α} {b : Binding α} {T U : Typ i} {v : Var β} {allowCap : Bool} :
    Var.WellFormed (allowCap := allowCap) (Γ ▷ ⟨α, x, b, T⟩ ++ Δ) v →
    Var.WellFormed (allowCap := allowCap) (Γ ▷ ⟨α, x, b, U⟩ ++ Δ) v
  := by
    cases v <;> simp [WellFormed,Assoc.dom]

  @[aesop unsafe]
  lemma fv_subset_dom :
    WellFormed (allowCap := allowCap) Γ v →
    fv v ⊆ dom Γ
  := by cases v <;> simp [WellFormed,fv]

  instance instWellFormedness {α : VarCat i} (allowCap : Bool) : WellFormedness i (Var α) where
    toWellScopedness := Var.WellScoped.instWellScopedness allowCap
    WellFormed := WellFormed (allowCap := allowCap)
    toWellScoped := toWellScoped (allowCap := allowCap)
    weaken := weaken (allowCap := allowCap)
end Var.WellFormed

def Cap.WellFormed (Γ : Env i) (C : Cap i) : Prop :=
  ∀ v ∈ C, Var.WellFormed (allowCap := true) Γ v

namespace Cap.WellFormed
  @[aesop safe]
  lemma toWellScoped {Γ : Env i} {C : Cap i} :
    Cap.WellFormed Γ C →
    Cap.WellScoped C
  := by
    intros C.WF v v.In
    eapply Var.WellFormed.toWellScoped
    apply C.WF; apply v.In

  @[simp]
  lemma empty {Γ : Env i} :
    WellFormed Γ ∅
  := by simp [WellFormed]

  @[simp]
  lemma cap {Γ : Env i} :
    WellFormed Γ {@Var.cap i _ rfl}
  := by simp [WellFormed,Var.WellFormed]

  @[simp]
  lemma singleton {Γ : Env i} :
    x ∈ dom Γ →
    WellFormed Γ {.free x}
  := by simp [WellFormed,Var.WellFormed]

  @[aesop safe]
  lemma union :
    WellFormed Γ C →
    WellFormed Γ D →
    WellFormed Γ (C ∪ D)
  := by
    simp [WellFormed]
    aesop

  lemma ignore_bindings {Γ Δ : Env i} {α : VarCat i} {x : Atom α} {b : Binding α} {T U : Typ i} {C : Cap i} :
    WellFormed (Γ ▷ ⟨α, x, b, T⟩ ++ Δ) C →
    WellFormed (Γ ▷ ⟨α, x, b, U⟩ ++ Δ) C
  := by
    intros WF
    intros v v.In
    exact Var.WellFormed.ignore_bindings (WF v v.In)

  @[aesop unsafe]
  lemma fv_subset_dom :
    WellFormed Γ C →
    fv C ⊆ dom Γ
  := by
    intros C.WF
    intros x x.In
    have x.WF : Var.WellFormed Γ (.free x) :=
      C.WF x (mem_fv_implies_mem_free x.In)
    apply Var.WellFormed.fv_subset_dom x.WF
    simp [Var.fv]

  @[aesop unsafe 40%]
  lemma weaken {Γ Θ Δ : Env i} :
    WellFormed (Γ ++ Δ) C →
    Env.Nodup (Γ ++ Θ ++ Δ) →
    WellFormed (Γ ++ Θ ++ Δ) C
  := fun WF nodup v In => Var.WellFormed.weaken (allowCap := true) (WF v In) nodup

  instance instWellFormedness : WellFormedness i (Cap i) where
    WellFormed := WellFormed
    toWellScoped := toWellScoped
    weaken := weaken
end Cap.WellFormed

@[aesop unsafe]
inductive Typ.WellFormed : Env i → Typ i → Prop where
  | var {Γ : Env i} {X : Atom (.tvar i)} {T : Typ i} :
      X <: T ∈ Γ ∨ (∃ (inst : HasFeature i type_bindings), X ≔ T ∈ Γ) →
      Typ.WellFormed Γ X
  | top {Γ : Env i} :
      Typ.WellFormed Γ .top
  | arr {Γ : Env i} {S : Typ i} {C : Cap i} {U : Typ i} (L : Finset (Atom (.var i))) :
      Typ.WellFormed Γ S →
      Typ.Shape S →
      Cap.WellFormed Γ C →
      (∀ x ∉ L, Typ.WellFormed (Γ ▷ x ⦂ .cap S C) (Typ.instantiateRecVar U 0 x)) →
      Typ.WellFormed Γ (.arr (.cap S C) U)
  | all {Γ : Env i} {k : TypeVarKind i} {S U : Typ i} (L : Finset (Atom (.tvar i))) :
      Typ.WellFormed Γ S →
      Typ.Shape S →
      (∀ X ∉ L, Typ.WellFormed (Γ ▷ X <: S) (Typ.instantiateRecTyp U 0 X)) →
      Typ.WellFormed Γ (.all k S U)
  | box {Γ : Env i} {T : Typ i} [HasFeature i box_type] :
      Typ.WellFormed Γ T →
      Typ.WellFormed Γ (@Typ.box i _ T)
  | cap {Γ : Env i} {S : Typ i} {C : Cap i} :
      WellFormed Γ S →
      Typ.Shape S →
      Cap.WellFormed Γ C →
      Typ.WellFormed Γ (.cap S C)

namespace Typ.WellFormed
  @[aesop safe]
  lemma toWellScoped {Γ : Env i} {T : Typ i} :
    WellFormed Γ T →
    WellScoped T
  := by
    intros T.WF
    simp [WellScoped]
    induction T.WF
    · case var Γ X S X.Mem =>
      exact Typ.Type.shape (Typ.Shape.var (by simp [Var.WellScoped]))
    · case top =>
      exact Typ.Type.shape Typ.Shape.top
    · case arr Γ S C U L S.WF S.Shape C.WF U.WF S.IH U.IH =>
      exact Typ.Type.shape (Typ.Shape.arr L S.Shape (Cap.WellFormed.toWellScoped C.WF) U.IH)
    · case all Γ k S U L S.WF S.Shape U.WF S.IH U.IH =>
      exact Typ.Type.shape (Typ.Shape.all L S.Shape U.IH)
    · case box Γ T _ T.WF T.IH =>
      exact Typ.Type.shape (Typ.Shape.box T.IH)
    · case cap Γ S C S.WF S.Shape C.WF S.IH =>
      apply Typ.Type.cap S.Shape (Cap.WellFormed.toWellScoped C.WF)

  lemma weaken {Γ Θ Δ : Env i} :
    WellFormed (Γ ++ Δ) T →
    Env.Nodup (Γ ++ Θ ++ Δ) →
    WellFormed (Γ ++ Θ ++ Δ) T
  := by
    intros WF nodup
    generalize Eq.gen : Γ ++ Δ = ΓΔ at WF
    induction WF generalizing Γ Δ <;> cases Eq.gen
    · case var X T X.Mem =>
      apply WellFormed.var (T := T)
      simp at X.Mem
      simp
      rcases X.Mem with ⟨⟨X.Mem⟩ | ⟨X.Mem⟩⟩ | ⟨HasTypeBindings, ⟨X.Mem⟩ | ⟨X.Mem⟩⟩
      · exact Or.inl (Or.inl (Or.inl X.Mem))
      · exact Or.inl (Or.inr X.Mem)
      · exact Or.inr ⟨HasTypeBindings, Or.inl (Or.inl X.Mem)⟩
      · exact Or.inr ⟨HasTypeBindings, Or.inr X.Mem⟩
    · case top => constructor
    · case arr S C U L S.Shape S.WF C.WF U.WF S.IH U.IH =>
      apply WellFormed.arr (L ∪ dom Γ ∪ dom Θ ∪ dom Δ)
      · exact S.IH nodup rfl
      · exact S.Shape
      · exact Cap.WellFormed.weaken C.WF nodup
      · intros x x.NotIn
        rw [<- Env.concat_cons]
        apply U.IH
        · clear * - x.NotIn
          aesop
        · apply Env.Nodup.cons nodup
          clear * - x.NotIn
          simp [Assoc.val]
          aesop
        · rfl
    · case all k S U L S.Shape S.WF U.WF S.IH U.IH =>
      apply WellFormed.all (L ∪ dom Γ ∪ dom Θ ∪ dom Δ)
      · exact S.IH nodup rfl
      · exact S.Shape
      · intros X X.NotIn
        rw [<- Env.concat_cons]
        apply U.IH
        · clear * - X.NotIn
          aesop
        · apply Env.Nodup.cons nodup
          clear * - X.NotIn
          simp only [Assoc.sub]
          aesop
        · rfl
    · case box T _ T.WF T.IH =>
      exact WellFormed.box (T.IH nodup rfl)
    · case cap S C S.Shape S.WF C.WF S.IH =>
      exact WellFormed.cap (S.IH nodup rfl) S.Shape (Cap.WellFormed.weaken C.WF nodup)

  lemma ignore_bindings {Γ Δ : Env i} {α : VarCat i} {x : Atom α} {b : Binding α} {T U S : Typ i} :
    WellFormed (Γ ▷ ⟨α, x, b, T⟩ ++ Δ) S →
    WellFormed (Γ ▷ ⟨α, x, b, U⟩ ++ Δ) S
  := by
    intros WF
    generalize Eq.gen : Γ ▷ ⟨α, x, b, T⟩ ++ Δ = Θ at WF
    induction WF generalizing Δ <;> cases Eq.gen
    · case var X S' X.Mem =>
      simp at X.Mem
      rcases X.Mem with ⟨⟨⟨X.MemΓ⟩ | ⟨Eq⟩⟩ | ⟨X.MemΔ⟩⟩ | ⟨_, ⟨⟨X.MemΓ⟩ | ⟨Eq⟩⟩ | ⟨X.MemΔ⟩⟩
      · apply WellFormed.var
        aesop
      · simp [Assoc.sub] at Eq
        split at Eq
        · case inl Eq.cat =>
          cases Eq.cat
          simp at Eq
          obtain ⟨Eq.name, Eq.binding, Eq.type⟩ := Eq
          cases Eq.name; cases Eq.binding; cases Eq.type
          apply WellFormed.var (T := U)
          aesop
        · case inr Neq.cat =>
          exfalso
          exact Eq
      · apply WellFormed.var
        aesop
      · apply WellFormed.var
        aesop
      · simp [Assoc.typ] at Eq
        split at Eq
        · case inl Eq.cat =>
          cases Eq.cat
          simp at Eq
          obtain ⟨Eq.name, Eq.binding, Eq.type⟩ := Eq
          cases Eq.name; cases Eq.binding; cases Eq.type
          apply WellFormed.var (T := U)
          aesop
        · case inr Neq.cat =>
          exfalso
          exact Eq
      · apply WellFormed.var
        aesop
    · case top =>
      apply WellFormed.top
    · case arr S C U L S.Shape S.WF C.WF U.WF S.IH U.IH =>
      apply WellFormed.arr L (S.IH rfl) S.Shape
      · exact Cap.WellFormed.ignore_bindings C.WF
      · intros x x.Fresh
        rw [<- Env.concat_cons]
        apply @U.IH x x.Fresh (Δ ▷ x ⦂ .cap S C) rfl
    · case all k S U L S.Shape S.WF U.WF S.IH U.IH =>
      apply WellFormed.all L (S.IH rfl) S.Shape
      intros X X.Fresh
      rw [<- Env.concat_cons]
      apply @U.IH X X.Fresh (Δ ▷ X <: S) rfl
    · case box T _ T.WF T.IH =>
      apply WellFormed.box (T.IH rfl)
    · case cap S C S.Shape S.WF C.WF S.IH =>
      apply WellFormed.cap (S.IH rfl) S.Shape
      apply Cap.WellFormed.ignore_bindings C.WF

  @[aesop unsafe]
  lemma fvVar_subset_fvVar_instantiateRecVar :
    fvVar T ⊆ fvVar (instantiateRecVar T k D)
  := by
    induction T generalizing k <;> simp [fvVar,instantiateRecVar]
    · case arr T U T.IH U.IH =>
      apply Finset.union_subset_union T.IH U.IH
    · case all k S U S.IH U.IH =>
      apply Finset.union_subset_union S.IH U.IH
    · case box T T.IH =>
      apply T.IH
    · case cap S C S.IH =>
      apply Finset.union_subset_union S.IH
      apply Cap.fv_subset_fv_instantiateRecCap

  @[aesop unsafe]
  lemma fvVar_subset_fvVar_instantiateRecTyp :
    fvVar T ⊆ fvVar (instantiateRecTyp T K U)
  := by
    induction T generalizing K <;> simp [fvVar,instantiateRecTyp]
    · case arr T U T.IH U.IH =>
      apply Finset.union_subset_union T.IH U.IH
    · case all k S U S.IH U.IH =>
      apply Finset.union_subset_union S.IH U.IH
    · case box T T.IH =>
      apply T.IH
    · case cap S C S.IH =>
      apply Finset.union_subset_union S.IH
      simp

  @[aesop unsafe]
  lemma fvVar_subset_dom :
    WellFormed Γ T →
    fvVar T ⊆ dom Γ
  := by
    intros T.WF
    induction T.WF <;> simp [fvVar]
    · case arr Γ S C U L S.WF S.Shape C.WF U.WF S.IH U.IH =>
      have C.Subset : Cap.fv C ⊆ dom Γ :=
        Cap.WellFormed.fv_subset_dom C.WF
      pick_fresh x ∉ L ∪ fvVar U ∪ dom Γ
      specialize U.IH x (by clear * - x.Fresh; aesop)
      simp [Assoc.dom] at U.IH
      apply Finset.union_subset S.IH
      apply Finset.union_subset C.Subset
      replace U.IH : fvVar U ⊆ dom Γ ∪ {x} := by
        trans fvVar (instantiateRecVar U 0 x)
        · exact fvVar_subset_fvVar_instantiateRecVar
        · exact U.IH
      rw [<- Finset.union_sdiff_cancel_right (s := dom Γ) (t := {x})]
      · apply Finset.subset_sdiff.mpr
        apply And.intro U.IH
        simp
        clear * - x.Fresh
        aesop
      · simp
        clear * - x.Fresh
        aesop
    · case all Γ k S U L S.WF S.Shape U.WF S.IH U.IH =>
      pick_fresh X ∉ L
      specialize U.IH X (by clear * - X.Fresh; aesop)
      simp [Assoc.dom] at U.IH
      apply Finset.union_subset S.IH
      trans fvVar (instantiateRecTyp U 0 (Typ.var (Var.free X)))
      · exact fvVar_subset_fvVar_instantiateRecTyp
      · exact U.IH
    · case box Γ T _ T.WF T.IH =>
      exact T.IH
    · case cap Γ S C S.WF S.Shape C.WF S.IH =>
      exact Finset.union_subset S.IH (Cap.WellFormed.fv_subset_dom C.WF)

  @[aesop unsafe]
  lemma fvTyp_subset_dom {Γ : Env i} {T : Typ i} :
    WellFormed Γ T →
    fvTyp T ⊆ dom Γ
  := by
    intros T.WF
    induction T.WF <;> simp
    · case var Γ X T X.Mem =>
      rcases X.Mem with ⟨X.Mem⟩ | ⟨X.Mem⟩
      · apply Env.dom_mem_iff.mpr
        exists .sub, T
      · decide HasTypeBindings : HasFeature i type_bindings
        · simp [HasTypeBindings] at X.Mem
        · apply Env.dom_mem_iff.mpr
          exists .typ, T
    · case arr Γ S C U L S.WF S.Shape C.WF U.WF S.IH U.IH =>
      have C.Subset : Cap.fv C ⊆ dom Γ :=
        Cap.WellFormed.fv_subset_dom C.WF
      pick_fresh x ∉ L
      specialize U.IH x (by clear * - x.Fresh; aesop)
      simp [Assoc.dom] at U.IH
      apply Finset.union_subset S.IH
      trans fvTyp (instantiateRecVar U 0 x)
      · exact fvTyp_subset_fvTyp_instantiateRecVar
      · exact U.IH
    · case all Γ k S U L S.WF S.Shape U.WF S.IH U.IH =>
      pick_fresh X ∉ L ∪ dom Γ ∪ fvTyp U
      specialize U.IH X (by clear * - X.Fresh; aesop)
      simp [Assoc.dom] at U.IH
      replace U.IH : fvTyp U ⊆ dom Γ ∪ {X} := by
        trans fvTyp (instantiateRecTyp U 0 (.var (Var.free X)))
        · exact fvTyp_subset_fvTyp_instantiateRecTyp
        · exact U.IH
      apply Finset.union_subset S.IH
      rw [<- Finset.union_sdiff_cancel_right (s := dom Γ) (t := {X})]
      · apply Finset.subset_sdiff.mpr
        apply And.intro U.IH
        simp
        clear * - X.Fresh
        aesop
      · simp
        clear * - X.Fresh
        aesop
    · case box Γ T _ T.WF T.IH =>
      exact T.IH
    · case cap Γ S C S.WF S.Shape C.WF S.IH =>
      exact S.IH

  lemma toType :
    Typ.WellFormed Γ T →
    Typ.Type T
  := by
    intros T.WF
    induction T.WF
    · case var =>
      exact Typ.Type.shape (Typ.Shape.var (by simp [Var.WellScoped]))
    · case top =>
      exact Typ.Type.shape Typ.Shape.top
    · case arr Γ S C U L S.WF S.Shape C.WF U.WF S.IH U.IH =>
      exact Typ.Type.shape (Typ.Shape.arr L S.Shape (Cap.WellFormed.toWellScoped C.WF) U.IH)
    · case all Γ S U k L S.WF S.Shape U.WF S.IH U.IH =>
      exact Typ.Type.shape (Typ.Shape.all _ S.Shape U.IH)
    · case box Γ T _ T.WF T.IH =>
      exact Typ.Type.shape (Typ.Shape.box T.IH)
    · case cap Γ S C S.WF S.Shape C.WF S.IH =>
      exact Typ.Type.cap S.Shape (Cap.WellFormed.toWellScoped C.WF)

  @[simp]
  instance instWellFormedness : WellFormedness i (Typ i) where
    WellFormed := WellFormed
    toWellScoped := toWellScoped
    weaken := weaken
end Typ.WellFormed

@[aesop unsafe]
inductive Assoc.WellFormed (Γ : Env i) : Assoc i → Prop where
  | val : ∀ {x S C},
    Typ.WellFormed Γ S →
    Typ.Shape S →
    Cap.WellFormed Γ C →
    Assoc.WellFormed Γ (x ⦂ .cap S C)
  | sub : ∀ {X S},
    Typ.WellFormed Γ S →
    Typ.Shape S →
    Assoc.WellFormed Γ (X <: S)
  | typ [HasFeature i type_bindings] : ∀ {X T},
    Typ.WellFormed Γ T →
    Assoc.WellFormed Γ (X ≔ T)

namespace Assoc.WellFormed
  lemma toWellScoped :
    WellFormed Γ a →
    WellScoped a
  := by
    intros WF
    induction WF
      <;> simp [Assoc.val,Assoc.sub,Assoc.typ]
      <;> apply Typ.WellFormed.toWellScoped (Γ := Γ)
    · case val =>
      constructor <;> assumption
    · case sub =>
      assumption
    · case typ =>
      assumption

  lemma weaken {Γ Θ Δ : Env i} :
    WellFormed (Γ ++ Δ) a →
    Env.Nodup (Γ ++ Θ ++ Δ) →
    WellFormed (Γ ++ Θ ++ Δ) a
  := by
    intros WF nodup
    induction WF
    · case val =>
      constructor
      · apply Typ.WellFormed.weaken (by assumption) nodup
      · assumption
      · apply Cap.WellFormed.weaken (by assumption) nodup
    · case sub =>
      constructor
      · apply Typ.WellFormed.weaken (by assumption) nodup
      · assumption
    · case typ =>
      constructor
      apply Typ.WellFormed.weaken (by assumption) nodup

  lemma ignore_bindings {Γ Δ : Env i} {α : VarCat i} {x : Atom α} {b : Binding α} {T U : Typ i} {a : Assoc i} :
    Assoc.WellFormed (Γ ▷ ⟨α, x, b, T⟩ ++ Δ) a →
    Assoc.WellFormed (Γ ▷ ⟨α, x, b, U⟩ ++ Δ) a
  := by
    intros WF
    induction WF
    · case val x S C S.WF S.Shape C.WF =>
      apply val
      · exact Typ.WellFormed.ignore_bindings S.WF
      · exact S.Shape
      · exact Cap.WellFormed.ignore_bindings C.WF
    · case sub X S S.WF S.Shape =>
      apply sub
      · exact Typ.WellFormed.ignore_bindings S.WF
      · exact S.Shape
    · case typ _ X T T.WF =>
      apply typ (Typ.WellFormed.ignore_bindings T.WF)

  @[simp]
  instance instWellFormedness : WellFormedness i (Assoc i) where
    WellFormed := WellFormed
    toWellScoped := toWellScoped
    weaken := weaken
end Assoc.WellFormed

@[aesop unsafe]
inductive Env.WellFormed : Env i → Prop where
  | nil : Env.WellFormed ∅
  | cons {Γ : Env i} {a : Assoc i} :
    Env.WellFormed Γ →
    a.name ∉ dom Γ →
    Assoc.WellFormed Γ a →
    Env.WellFormed (Γ ▷ a)

namespace Env.WellFormed
  lemma ignore_bindings {Γ Δ : Env i} {α : VarCat i} {x : Atom α} {b : Binding α} {T U : Typ i} :
    Assoc.WellFormed Γ ⟨α, x, b, U⟩ →
    WellFormed (Γ ▷ ⟨α, x, b, T⟩ ++ Δ) →
    WellFormed (Γ ▷ ⟨α, x, b, U⟩ ++ Δ)
  := by
    intros xU.WF ΓTΔ.WF
    induction Δ
    · case nil =>
      simp at ΓTΔ.WF
      cases ΓTΔ.WF
      apply cons <;> assumption
    · case cons Δ a IH =>
      simp at ΓTΔ.WF
      cases ΓTΔ.WF
      simp
      apply cons
      · apply IH; assumption
      · simp at *; assumption
      · apply Assoc.WellFormed.ignore_bindings
        assumption

  lemma Nodup {Γ : Env i} :
    Env.WellFormed Γ →
    Env.Nodup Γ
  := by
    intros WF
    induction WF
    · case nil => simp
    · case cons Γ a a.WF a.NotIn Γ.WF IH =>
      apply Env.Nodup.cons IH a.NotIn

  lemma mem {Γ : Env i} {a : Assoc i} :
    Env.WellFormed Γ →
    a ∈ Γ →
    Assoc.WellFormed Γ a
  := by
    intros Γ.WF a.In
    induction Γ.WF
    · case nil => simp at a.In
    · case cons Γ b Γ.WF b.NotIn b.WF IH =>
      simp only [Env.mem_cons] at a.In
      cases a.In
      · case inl a.In =>
        change WellFormedness.WellFormed (self := Assoc.WellFormed.instWellFormedness) (Γ ▷ b) a
        apply WellFormedness.weaken_cons
        apply Nodup Γ.WF
        · exact b.NotIn
        · exact IH a.In
      · case inr Eq.a =>
        cases Eq.a
        change WellFormedness.WellFormed (self := Assoc.WellFormed.instWellFormedness) (Γ ▷ a) a
        apply WellFormedness.weaken_cons (Nodup Γ.WF) b.NotIn
        exact b.WF

  lemma mid {Γ : Env i} {a : Assoc i} {Δ : Env i} :
    Env.WellFormed (Γ ▷ a ++ Δ) →
    Assoc.WellFormed Γ a
  := by
    intros WF
    induction Δ
    · case nil =>
      cases WF
      assumption
    · case cons Δ b IH =>
      cases WF
      apply IH
      assumption

  lemma split {Θ : Env i} {a : Assoc i} :
    WellFormed Θ →
    a ∈ Θ →
    ∃ Γ Δ, Θ = Γ ▷ a ++ Δ
  := by
    intros Θ.WF a.Mem
    induction Θ.WF <;> simp at a.Mem
    case cons Θ b Θ.WF b.NotIn b.WF IH =>
    cases a.Mem
    · case inl a.Mem =>
      obtain ⟨Γ, ⟨Δ, Eq⟩⟩ := IH a.Mem
      exists Γ, Δ ▷ b
      simp [Eq]
    · case inr a.Eq =>
      rw [a.Eq]
      exists Θ, ∅

  lemma inversion_val {Γ Δ : Env i} {x : Atom (.var i)} {S : Typ i} {C : Cap i} :
    WellFormed (Γ ▷ x ⦂ .cap S C ++ Δ) →
      Typ.WellFormed Γ S
    ∧ Typ.Shape S
    ∧ Cap.WellFormed Γ C
    ∧ x ∉ Typ.fvVar (.cap S C)
  := by
    intros Θ.WF
    generalize Eq.gen : Γ ▷ x ⦂ .cap S C ++ Δ = Θ at Θ.WF
    induction Θ.WF generalizing Δ <;> simp at Eq.gen
    case cons Θ a Θ.WF a.NotIn a.WF IH =>
    cases Δ <;> simp [-Typ.fvVar] at *
    · case nil =>
      obtain ⟨Eq.Θ, Eq.a⟩ := Eq.gen
      cases Eq.Θ
      cases Eq.a
      simp [-Typ.fvVar] at *
      cases a.WF
      case val S.WF S.Shape C.WF =>
      apply And.intro S.WF (And.intro S.Shape (And.intro C.WF _))
      revert a.NotIn
      contrapose
      simp [-Typ.fvVar]
      apply Typ.WellFormed.fvVar_subset_dom
      apply Typ.WellFormed.cap S.WF S.Shape C.WF
    · case cons Δ b _ =>
      obtain ⟨Eq.Θ,Eq.a⟩ := Eq.gen
      cases Eq.Θ
      cases Eq.a
      apply IH rfl

  lemma split_val {Θ : Env i} {x : Atom (.var i)} {S : Typ i} {C : Cap i} :
    WellFormed Θ →
    x ⦂ .cap S C ∈ Θ →
    ∃ Γ Δ, Θ = Γ ▷ x ⦂ .cap S C ++ Δ
         ∧ Typ.WellFormed Γ S
         ∧ Typ.Shape S
         ∧ Cap.WellFormed Γ C
         ∧ x ∉ Typ.fvVar (.cap S C)
  := by
    intros Θ.WF a.Mem
    obtain ⟨Γ, ⟨Δ, Θ.Eq⟩⟩ := split Θ.WF a.Mem
    exists Γ, Δ
    cases Θ.Eq
    simp [-Typ.fvVar]
    apply inversion_val Θ.WF

  lemma inversion_sub {Γ Δ : Env i} {X : Atom (.tvar i)} {U : Typ i} :
    WellFormed (Γ ▷ X <: U ++ Δ) →
      Typ.WellFormed Γ U
    ∧ Typ.Shape U
    ∧ X ∉ Typ.fvTyp U
  := by
    intros Θ.WF
    generalize Eq.gen : Γ ▷ X <: U ++ Δ = Θ at Θ.WF
    induction Θ.WF generalizing Δ <;> simp at Eq.gen
    case cons Θ a Θ.WF a.NotIn a.WF IH =>
    cases Δ <;> simp at *
    · case nil =>
      obtain ⟨Eq.Θ, Eq.a⟩ := Eq.gen
      cases Eq.Θ
      cases Eq.a
      simp at *
      cases a.WF
      case sub U.WF U.Shape =>
      apply And.intro U.WF (And.intro U.Shape _)
      revert a.NotIn
      contrapose
      simp
      apply Typ.WellFormed.fvTyp_subset_dom
      apply U.WF
    · case cons Δ b _ =>
      obtain ⟨Eq.Θ,Eq.a⟩ := Eq.gen
      cases Eq.Θ
      cases Eq.a
      apply IH rfl

  lemma split_sub {Θ : Env i} {X : Atom (.tvar i)} {U : Typ i} :
    WellFormed Θ →
    X <: U ∈ Θ →
    ∃ Γ Δ, Θ = Γ ▷ X <: U ++ Δ
         ∧ Typ.WellFormed Γ U
         ∧ Typ.Shape U
         ∧ X ∉ Typ.fvTyp U
  := by
    intros Θ.WF a.Mem
    obtain ⟨Γ, ⟨Δ, Θ.Eq⟩⟩ := split Θ.WF a.Mem
    exists Γ, Δ
    cases Θ.Eq
    simp
    apply inversion_sub Θ.WF

  lemma inversion_typ [HasFeature i type_bindings] {Γ Δ : Env i} {X : Atom (.tvar i)} {U : Typ i} :
    WellFormed (Γ ▷ X ≔ U ++ Δ) →
      Typ.WellFormed Γ U
    ∧ X ∉ Typ.fvTyp U
  := by
    intros Θ.WF
    generalize Eq.gen : Γ ▷ X ≔ U ++ Δ = Θ at Θ.WF
    induction Θ.WF generalizing Δ <;> simp at Eq.gen
    case cons Θ a Θ.WF a.NotIn a.WF IH =>
    cases Δ <;> simp at *
    · case nil =>
      obtain ⟨Eq.Θ, Eq.a⟩ := Eq.gen
      cases Eq.Θ
      cases Eq.a
      simp at *
      cases a.WF
      case typ U.WF =>
      apply And.intro U.WF
      revert a.NotIn
      contrapose
      simp
      apply Typ.WellFormed.fvTyp_subset_dom
      apply U.WF
    · case cons Δ b _ =>
      obtain ⟨Eq.Θ,Eq.a⟩ := Eq.gen
      cases Eq.Θ
      cases Eq.a
      apply IH rfl

  lemma split_typ [HasFeature i type_bindings] {Θ : Env i} {X : Atom (.tvar i)} {U : Typ i} :
    WellFormed Θ →
    X ≔ U ∈ Θ →
    ∃ Γ Δ, Θ = Γ ▷ X ≔ U ++ Δ
         ∧ Typ.WellFormed Γ U
         ∧ X ∉ Typ.fvTyp U
  := by
    intros Θ.WF a.Mem
    obtain ⟨Γ, ⟨Δ, Θ.Eq⟩⟩ := split Θ.WF a.Mem
    exists Γ, Δ
    cases Θ.Eq
    simp
    apply inversion_typ Θ.WF

  lemma concat_left {Γ Δ : Env i} :
    WellFormed (Γ ++ Δ) →
    WellFormed Γ
  := by
    intros WF
    induction Δ
    · case nil =>
      simp at WF
      exact WF
    · case cons Δ a IH =>
      cases WF
      apply IH
      assumption
end Env.WellFormed

namespace Env.Nodup
  @[aesop safe]
  lemma substitutionCap :
    Nodup (Γ ▷ z ⦂ U ++ Δ) →
    Nodup (Γ ++ Δ.substituteCap z D)
  := by
    intros nodup
    generalize Eq.gen : Γ ▷ z ⦂ U ++ Δ = Θ at nodup
    induction nodup generalizing Γ Δ <;> simp at *
    case cons Θ a nodup a.NotIn IH =>
    cases Δ
    · case nil =>
      simp at *
      rw [Eq.gen.1]
      exact nodup
    · case cons Δ b  _ =>
      simp at *
      obtain ⟨Eq1, ⟨Eq2, Eq3⟩⟩ := Eq.gen
      apply Nodup.cons
      · apply IH Eq1
      · rw [<- Eq1] at a.NotIn
        simp at a.NotIn
        cases a <;> simp [Assoc.substituteCap] at * <;> aesop

    @[aesop safe]
  lemma substitutionVal :
    Nodup (Γ ▷ z ⦂ U ++ Δ) →
    Nodup (Γ ++ Δ.substituteVar z u)
  := substitutionCap

  @[aesop safe]
  lemma substitutionSub :
    Nodup (Γ ▷ Z <: U ++ Δ) →
    Nodup (Γ ++ Δ.substituteTyp Z U)
  := by
    intros nodup
    generalize Eq.gen : Γ ▷ Z <: U ++ Δ = Θ at nodup
    induction nodup generalizing Γ Δ <;> simp at *
    case cons Θ a nodup a.NotIn IH =>
    cases Δ
    · case nil =>
      simp at *
      rw [Eq.gen.1]
      exact nodup
    · case cons Δ b  _ =>
      simp at *
      obtain ⟨Eq1, ⟨Eq2, Eq3⟩⟩ := Eq.gen
      apply Nodup.cons
      · apply IH Eq1
      · rw [<- Eq1] at a.NotIn
        simp at a.NotIn
        cases a <;> simp [Assoc.substituteTyp] at * <;> aesop

  @[aesop safe]
  lemma substitutionTyp [HasFeature i type_bindings] {Γ Δ : Env i} {Z : Atom (.tvar i)} {U : Typ i}:
    Nodup (Γ ▷ Z ≔ U ++ Δ) →
    Nodup (Γ ++ Δ.substituteTyp Z U)
  := by
    intros nodup
    generalize Eq.gen : Γ ▷ Z ≔ U ++ Δ = Θ at nodup
    induction nodup generalizing Γ Δ <;> simp at *
    case cons Θ a nodup a.NotIn IH =>
    cases Δ
    · case nil =>
      simp at *
      rw [Eq.gen.1]
      exact nodup
    · case cons Δ b  _ =>
      simp at *
      obtain ⟨Eq1, ⟨Eq2, Eq3⟩⟩ := Eq.gen
      apply Nodup.cons
      · apply IH Eq1
      · rw [<- Eq1] at a.NotIn
        simp at a.NotIn
        cases a <;> simp [Assoc.substituteTyp] at * <;> aesop
end Env.Nodup

namespace Var.WellFormed
  @[aesop unsafe]
  lemma substitutionCap {Γ Δ : Env i} {z : Atom (.var i)} {v : Var (.var i)} {u : Var (.var i)} {D : Cap i} :
    WellFormed (allowCap := allowCap) Γ u →
    Cap.WellFormed Γ D →
    WellFormed (allowCap := allowCap) (Γ ▷ z ⦂ U ++ Δ) v →
    WellFormed (allowCap := allowCap) (Γ ++ Δ.substituteCap z D) (v.substitute z u)
  := by
    intros u.WF D.WF
    cases v <;> simp [WellFormed,substitute]
    case free x =>
    cases decEq x z
    · case isFalse Neq =>
      simp [Neq,Assoc.dom]
    · case isTrue Eq =>
      simp [Eq,Assoc.dom]
      aesop

  @[aesop unsafe]
  lemma substitutionVal {Γ Δ : Env i} {z : Atom (.var i)} {v : Var (.var i)} {u : Var (.var i)} :
    WellFormed (allowCap := allowCap) Γ u →
    WellFormed (allowCap := allowCap) (Γ ▷ z ⦂ U ++ Δ) v →
    WellFormed (allowCap := allowCap) (Γ ++ Δ.substituteVar z u) (v.substitute z u)
  := by
    intros u.WF v.WF
    apply substitutionCap u.WF _ v.WF
    simp [Cap.WellFormed]
    exact Var.WellFormed.map_allowCap (by simp) u.WF

  @[aesop unsafe]
  lemma substitutionSub {Γ Δ : Env i} {Z : Atom (.tvar i)} {v : Var (.var i)} {U : Typ i} :
    Typ.WellFormed Γ U →
    WellFormed (allowCap := allowCap) (Γ ▷ Z <: U ++ Δ) v →
    WellFormed (allowCap := allowCap) (Γ ++ Δ.substituteTyp Z U) v
  := by
    cases v <;> simp [WellFormed,substitute,Assoc.dom]
end Var.WellFormed

namespace Cap.WellFormed
  @[aesop unsafe]
  lemma substitutionCap {Γ Δ : Env i} {z : Atom (.var i)} {U : Typ i} {C D : Cap i} :
    Env.Nodup (Γ ▷ z ⦂ U ++ Δ) →
    WellFormed Γ D →
    WellFormed (Γ ▷ z ⦂ U ++ Δ) C →
    WellFormed (Γ ++ Δ.substituteCap z D) (C.substituteCap z D)
  := by
    intros nodup D.WF C.WF
    simp only [substituteCap]
    split
    · case inl z.InC =>
      apply Cap.WellFormed.union
      · intros v v.In
        simp at v.In
        obtain ⟨v.In, v.Neq⟩ := v.In
        have z.NotInV : z ∉ Var.fv v := by
          cases v <;> simp at v.Neq <;> simp [Var.fv]; aesop
        have v.WF := C.WF v v.In
        cases v <;> simp [Var.WellFormed] at *
        case a.intro.free y =>
        rcases v.WF with ⟨y.InΓ⟩ | ⟨⟨y.Eq⟩ | ⟨y.InΔ⟩⟩
        · exact Or.inl y.InΓ
        · exfalso
          simp [Assoc.dom] at y.Eq
          exact v.Neq y.Eq
        · exact Or.inr y.InΔ
      · rw [<- Env.concat_nil (Γ := Γ ++ Δ.substituteCap z D)]
        apply Cap.WellFormed.weaken
        · simp
          exact D.WF
        · exact Env.Nodup.substitutionCap nodup
    · case inr z.NotInC =>
      intros v v.In
      have v.WF := C.WF v v.In
      simp [Var.WellFormed]
      cases v <;> simp [Var.WellFormed] at *
      case free y =>
      rcases v.WF with ⟨y.InΓ⟩ | ⟨⟨y.Eq⟩ | ⟨y.InΔ⟩⟩
      · exact Or.inl y.InΓ
      · simp [Assoc.dom] at y.Eq
        cases y.Eq
        exfalso
        exact z.NotInC v.In
      · exact Or.inr y.InΔ

  @[aesop unsafe]
  lemma substitutionVal {Γ Δ : Env i} {z : Atom (.var i)} {U : Typ i} {C : Cap i} {u : Var (.var i)}:
    Env.Nodup (Γ ▷ z ⦂ U ++ Δ) →
    Var.WellFormed (allowCap := allowCap) Γ u →
    WellFormed (Γ ▷ z ⦂ U ++ Δ) C →
    WellFormed (Γ ++ Δ.substituteVar z u) (C.substituteVar z u)
  := by
    intros nodup u.WF C.WF
    apply substitutionCap nodup _ C.WF
    simp [WellFormed]
    exact Var.WellFormed.map_allowCap (by simp) u.WF

  @[aesop unsafe]
  lemma substitutionSub {Γ Δ : Env i} {Z : Atom (.tvar i)} {U : Typ i} {C : Cap i} :
    Typ.WellFormed Γ U →
    WellFormed (Γ ▷ Z <: U ++ Δ) C →
    WellFormed (Γ ++ Δ.substituteTyp Z U) C
  := by
    simp [WellFormed] at *
    intros U.WF C.WF v v.In
    apply Var.WellFormed.substitutionSub U.WF (C.WF v v.In)
end Cap.WellFormed

namespace Typ.WellFormed
  @[aesop unsafe]
  private lemma substitutionCap_aux {Γ Δ : Env i} {z : Atom (.var i)} {U : Typ i} {D : Cap i} {T : Typ i} :
    Env.Nodup (Γ ▷ z ⦂ U ++ Δ) →
    Cap.WellFormed Γ D →
    WellFormed (Γ ▷ z ⦂ U ++ Δ) T →
    WellFormed (Γ ++ Δ.substituteCap z D) (T.substituteCap z D)
  := by
    intros nodup D.WF T.WF
    generalize Eq.gen : Γ ▷ z ⦂ U ++ Δ = Θ at T.WF
    induction T.WF generalizing Δ <;> cases Eq.gen <;> simp [substituteVar]
    · case var X T X.Mem =>
      simp at X.Mem
      rcases X.Mem with ⟨⟨X.Mem⟩ | ⟨X.Mem⟩⟩ | ⟨_, ⟨X.Mem⟩ | ⟨X.Mem⟩⟩
        <;> apply var <;> aesop
    · case top =>
      exact top
    · case arr S C T L S.Shape S.WF C.WF T.WF S.IH T.IH =>
      apply arr (L ∪ Env.dom Γ ∪ Env.dom Δ ∪ {z})
      · exact S.IH nodup rfl
      · exact Shape_substituteCap (Cap.WellFormed.toWellScoped D.WF) S.Shape
      · exact Cap.WellFormed.substitutionCap nodup D.WF C.WF
      · intros x x.Fresh
        unfold instantiateRecVar
        rw [<- Cap.substituteCap_fresh (x := z) (D := D) (C := {.free x}) (by simp [Cap.fv,Var.fv]; clear * - x.Fresh; aesop)]
        rw [<- substituteCap_instantiateRecCap (Cap.WellFormed.toWellScoped D.WF)]
        conv in (Γ ++ _) ▷ _ =>
          change (Γ ++ (Δ ▷ x ⦂ .cap S C).substituteCap z D)
          rfl
        apply T.IH
        · clear * - x.Fresh; aesop
        · change Env.Nodup ((Γ ▷ z ⦂ U ++ Δ) ▷ x ⦂ Typ.cap S C)
          apply Env.Nodup.cons nodup
          simp [Assoc.dom]
          clear * - x.Fresh; aesop
        · rfl
    · case all k S U L S.Shape S.WF T.WF S.IH T.IH =>
      apply all (L ∪ Env.dom Γ ∪ Env.dom Δ)
      · apply S.IH nodup rfl
      · apply Shape_substituteCap (Cap.WellFormed.toWellScoped D.WF) S.Shape
      · intros X X.Fresh
        rw [<- Typ.substituteCap_fresh (x := z) (D := D) (T := .var (Var.free X)) (by clear * - X.Fresh; aesop)]
        rw [<- substituteCap_instantiateRecTyp]
        conv in (Γ ++ _) ▷ _ =>
          change (Γ ++ (Δ ▷ X <: S).substituteCap z D)
          rfl
        apply T.IH
        · clear * - X.Fresh; aesop
        · change Env.Nodup ((Γ ▷ z ⦂ _ ++ Δ) ▷ X <: S)
          apply Env.Nodup.cons nodup
          simp [Assoc.dom]
          clear * - X.Fresh; aesop
        · rfl
    · case box T _ T.WF T.IH =>
      exact box (T.IH nodup rfl)
    · case cap S C S.Shape S.WF C.WF S.IH =>
      apply cap
      · exact S.IH nodup rfl
      · exact Typ.Shape_substituteCap (Cap.WellFormed.toWellScoped D.WF) S.Shape
      · exact Cap.WellFormed.substitutionCap nodup D.WF C.WF

  @[aesop unsafe]
  private lemma substitutionSubTVar_aux {Γ Δ : Env i} {Z : Atom (.tvar i)} {V : Var (.tvar i)} {U : Typ i} :
    Env.Nodup (Γ ▷ Z <: U ++ Δ) →
    Typ.WellFormed Γ U →
    WellFormed (Γ ▷ Z <: U ++ Δ) V →
    Typ.WellFormed (Γ ++ Δ.substituteTyp Z U) (V.subst Z U)
  := by
    intros nodup U.WF V.WF
    cases V.WF
    case var X T X.Mem =>
    simp [Var.subst]
    split
    · case inl Eq =>
      cases Eq
      change WellFormed (Γ ++ Δ.substituteTyp Z U ++ ∅) U
      apply Typ.WellFormed.weaken
      · simp
        exact U.WF
      · exact Env.Nodup.substitutionSub nodup
    · case inr Neq =>
      simp [Neq] at X.Mem
      rcases X.Mem with ⟨⟨X.Mem⟩ | ⟨X.Mem⟩⟩ | ⟨HasTypeBindings, ⟨X.Mem⟩ | ⟨X.Mem⟩⟩
      · apply var (T := T)
        simp
        apply Or.inl (Or.inl X.Mem)
      · apply var (T := substituteTyp T Z U)
        simp
        apply Or.inl (Or.inr _)
        exists { cat := VarCat.tvar i, name := X, binding := Binding.sub, type := T }
      · apply var (T := T)
        simp
        apply Or.inr ⟨HasTypeBindings, Or.inl X.Mem⟩
      · apply var (T := substituteTyp T Z U)
        simp
        apply Or.inr
        exists HasTypeBindings
        apply Or.inr
        exists { cat := VarCat.tvar i, name := X, binding := Binding.typ, type := T }

  @[aesop safe apply]
  private lemma _root_.Var.subst_fresh {V : Var (.tvar i)} {U : Typ i} {X : Atom (.tvar i)} :
    X ∉ Var.fv V →
    Var.subst V X U = .var V
  := by simp [Var.fv,Var.subst]; aesop

  @[aesop unsafe]
  private lemma substitutionSub_aux {Γ Δ : Env i} {Z : Atom (.tvar i)} {T : Typ i} {U : Typ i} :
    Env.Nodup (Γ ▷ Z <: U ++ Δ) →
    WellFormed Γ U →
    Shape U →
    WellFormed (Γ ▷ Z <: U ++ Δ) T →
    WellFormed (Γ ++ Δ.substituteTyp Z U) (T.substituteTyp Z U)
  := by
    intros nodup U.WF U.Shape T.WF
    generalize Eq.gen : Γ ▷ Z <: U ++ Δ = Θ at T.WF
    induction T.WF generalizing Δ <;> cases Eq.gen <;> simp only [substituteTyp]
    · case var X S X.Mem =>
      exact substitutionSubTVar_aux nodup U.WF (var X.Mem)
    · case top =>
      exact top
    · case arr S C T L S.Shape S.WF C.WF T.WF S.IH T.IH =>
      apply arr (L ∪ Env.dom Γ ∪ Env.dom Δ)
      · exact S.IH nodup rfl
      · exact Shape_substituteTyp U.Shape S.Shape
      · exact Cap.WellFormed.substitutionSub U.WF C.WF
      · intros x x.Fresh
        rw [<- substituteTyp_instantiateRecVar (Typ.WellFormed.toWellScoped U.WF)]
        conv in (Γ ++ _) ▷ _ =>
          change (Γ ++ Env.substituteTyp (Δ ▷ x ⦂ .cap S C) Z U)
          rfl
        apply T.IH
        · clear * - x.Fresh; aesop
        · change Env.Nodup ((Γ ▷ Z <: U ++ Δ) ▷ x ⦂ Typ.cap S C)
          apply Env.Nodup.cons nodup
          simp [Assoc.dom]
          clear * - x.Fresh; aesop
        · rfl
    · case all k S T L S.Shape S.WF T.WF S.IH T.IH =>
      apply all (L ∪ Env.dom Γ ∪ {Z} ∪ Env.dom Δ)
      · exact S.IH nodup rfl
      · exact Shape_substituteTyp U.Shape S.Shape
      · intros X X.Fresh
        rw [<- Typ.substituteTyp_fresh (X := Z) (U := U) (T := .var (Var.free X)) (by clear * - X.Fresh; aesop)]
        rw [<- substituteTyp_instantiateRecTyp (Typ.WellFormed.toWellScoped U.WF)]
        conv in (Γ ++ _) ▷ _ =>
          change (Γ ++ Env.substituteTyp (Δ ▷ X <: S) Z U)
          rfl
        apply T.IH
        · clear * - X.Fresh; aesop
        · change Env.Nodup ((Γ ▷ Z <: U ++ Δ) ▷ X <: S)
          apply Env.Nodup.cons nodup
          simp [Assoc.dom]
          clear * - X.Fresh; aesop
        · rfl
    · case box T _ T.WF T.IH =>
      exact box (T.IH nodup rfl)
    · case cap S C S.Shape S.WF C.WF S.IH =>
      apply cap
      · exact S.IH nodup rfl
      · exact Typ.Shape_substituteTyp U.Shape S.Shape
      · exact Cap.WellFormed.substitutionSub U.WF C.WF
end Typ.WellFormed

namespace Assoc.WellFormed
  @[aesop unsafe]
  lemma substitutionCap {Γ Δ : Env i} {a : Assoc i} {z : Atom (.var i)} {D : Cap i} :
    Env.WellFormed (Γ ▷ z ⦂ U ++ Δ) →
    Cap.WellFormed Γ D →
    WellFormed (Γ ▷ z ⦂ U ++ Δ) a →
    WellFormed (Γ ++ Δ.substituteCap z D) (a.substituteCap z D)
  := by
    intros Θ.WF D.WF a.WF
    cases a.WF <;> simp [WellFormed,substituteVar]
    · case val x S C S.WF S.Shape C.WF =>
      apply val
      · apply Typ.WellFormed.substitutionCap_aux
        · exact Env.WellFormed.Nodup Θ.WF
        · exact D.WF
        · assumption
      · exact Typ.Shape_substituteCap (Cap.WellFormed.toWellScoped D.WF) S.Shape
      · exact Cap.WellFormed.substitutionCap (Env.WellFormed.Nodup Θ.WF) D.WF C.WF
    · case sub X S S.WF S.Shape =>
      apply sub
      · apply Typ.WellFormed.substitutionCap_aux
        · exact Env.WellFormed.Nodup Θ.WF
        · exact D.WF
        · assumption
      · apply Typ.Shape_substituteCap (Cap.WellFormed.toWellScoped D.WF) S.Shape
    · case typ X T T.WF =>
      apply typ
      apply Typ.WellFormed.substitutionCap_aux
      · exact Env.WellFormed.Nodup Θ.WF
      · exact D.WF
      · assumption

  @[aesop unsafe]
  lemma substitutionSub {Γ Δ : Env i} {a : Assoc i} {Z : Atom (.tvar i)} {U : Typ i} :
    Env.WellFormed (Γ ▷ Z <: U ++ Δ) →
    WellFormed (Γ ▷ Z <: U ++ Δ) a →
    WellFormed (Γ ++ Δ.substituteTyp Z U) (a.substituteTyp Z U)
  := by
    intros Θ.WF a.WF

    have ZU.WF : WellFormed Γ (Z <: U) :=
      Env.WellFormed.mid Θ.WF
    have U.WF : Typ.WellFormed Γ U := by
      cases ZU.WF; assumption
    have U.Shape : Typ.Shape U := by
      cases ZU.WF; assumption

    cases a.WF <;> simp [WellFormed,substituteVar]
    · case val x S C S.WF S.Shape C.WF =>
      apply val
      · apply Typ.WellFormed.substitutionSub_aux
        · exact Env.WellFormed.Nodup Θ.WF
        · exact U.WF
        · exact U.Shape
        · exact S.WF
      · apply Typ.Shape_substituteTyp <;> aesop
      · apply Cap.WellFormed.substitutionSub U.WF C.WF
    · case sub X S S.WF S.Shape =>
      apply sub
      · apply Typ.WellFormed.substitutionSub_aux
        · exact Env.WellFormed.Nodup Θ.WF
        · exact U.WF
        · assumption
        · exact S.WF
      · apply Typ.Shape_substituteTyp <;> aesop
    · case typ X T T.WF =>
      apply typ
      apply Typ.WellFormed.substitutionSub_aux
      · exact Env.WellFormed.Nodup Θ.WF
      · exact U.WF
      · assumption
      · exact T.WF
end Assoc.WellFormed

namespace Env.WellFormed
  @[aesop safe]
  lemma substitutionCap {Γ : Env i} {z : Atom (.var i)} {U : Typ i} {Δ : Env i} {D : Cap i} :
    Cap.WellFormed Γ D →
    WellFormed (Γ ▷ z ⦂ U ++ Δ) →
    WellFormed (Γ ++ Δ.substituteCap z D)
  := by
    intros D.WF Θ.WF
    generalize Eq.gen : Γ ▷ z ⦂ U ++ Δ = Θ at Θ.WF
    induction Θ.WF generalizing Γ Δ <;> simp at *
    case cons Θ a Θ.WF a.NotIn a.WF IH =>
    cases Δ
    · case nil =>
      simp at *
      rw [Eq.gen.1]
      exact Θ.WF
    · case cons Δ b  _ =>
      simp at *
      obtain ⟨Eq1, ⟨Eq2, Eq3⟩⟩ := Eq.gen
      rw [<- Eq1] at Θ.WF a.WF a.NotIn
      apply cons
      · apply IH D.WF Eq1
      · simp at a.NotIn
        cases a <;> simp [Assoc.substituteCap] at * <;> aesop
      · exact Assoc.WellFormed.substitutionCap Θ.WF D.WF a.WF

  @[aesop safe]
  lemma substitutionVal {Γ : Env i} {z : Atom (.var i)} {U : Typ i} {Δ : Env i} {u : Var (.var i)} :
    Var.WellFormed (allowCap := allowCap) Γ u →
    WellFormed (Γ ▷ z ⦂ U ++ Δ) →
    WellFormed (Γ ++ Δ.substituteVar z u)
  := by
    intros u.WF Θ.WF
    apply substitutionCap _ Θ.WF
    simp [Cap.WellFormed]
    exact Var.WellFormed.map_allowCap (by simp) u.WF

  @[aesop safe]
  lemma substitutionSub :
    WellFormed (Γ ▷ Z <: U ++ Δ) →
    WellFormed (Γ ++ Δ.substituteTyp Z U)
  := by
    intros Θ.WF
    generalize Eq.gen : Γ ▷ Z <: U ++ Δ = Θ at Θ.WF
    induction Θ.WF generalizing Γ Δ <;> simp at *
    case cons Θ a Θ.WF a.NotIn a.WF IH =>
    cases Δ
    · case nil =>
      simp at *
      rw [Eq.gen.1]
      exact Θ.WF
    · case cons Δ b  _ =>
      simp at *
      obtain ⟨Eq1, ⟨Eq2, Eq3⟩⟩ := Eq.gen
      rw [<- Eq1] at Θ.WF a.WF a.NotIn
      apply cons
      · apply IH Eq1
      · simp at a.NotIn
        cases a <;> simp [Assoc.substituteTyp] at * <;> aesop
      · exact Assoc.WellFormed.substitutionSub Θ.WF a.WF
end Env.WellFormed

namespace Typ.WellFormed
  @[aesop unsafe]
  lemma substitutionCap {Γ Δ : Env i} {z : Atom (.var i)} {U : Typ i} {D : Cap i} {T : Typ i} :
    Env.WellFormed (Γ ▷ z ⦂ U ++ Δ) →
    Cap.WellFormed Γ D →
    WellFormed (Γ ▷ z ⦂ U ++ Δ) T →
    WellFormed (Γ ++ Δ.substituteCap z D) (T.substituteCap z D)
  := by
    intros Θ.WF D.WF T.WF
    exact substitutionCap_aux (Env.WellFormed.Nodup Θ.WF) D.WF T.WF

  @[aesop unsafe]
  lemma substitutionVal {Γ Δ : Env i} {z : Atom (.var i)} {U : Typ i} {u : Var (.var i)} {T : Typ i} :
    Env.WellFormed (Γ ▷ z ⦂ U ++ Δ) →
    Var.WellFormed (allowCap := allowCap) Γ u →
    WellFormed (Γ ▷ z ⦂ U ++ Δ) T →
    WellFormed (Γ ++ Δ.substituteVar z u) (T.substituteVar z u)
  := by
    intros Θ.WF u.WF T.WF
    apply substitutionCap Θ.WF _ T.WF
    simp [Cap.WellFormed]
    exact Var.WellFormed.map_allowCap (by simp) u.WF

  @[aesop unsafe]
  lemma substitutionSub {Γ Δ : Env i} {Z : Atom (.tvar i)} {T : Typ i} {U : Typ i} :
    Env.WellFormed (Γ ▷ Z <: U ++ Δ) →
    WellFormed (Γ ▷ Z <: U ++ Δ) T →
    WellFormed (Γ ++ Δ.substituteTyp Z U) (T.substituteTyp Z U)
  := by
    intros Θ.WF T.WF
    have ZU.WF : Assoc.WellFormed Γ (Z <: U) :=
      Env.WellFormed.mid Θ.WF
    have U.WF : Typ.WellFormed Γ U := by
      cases ZU.WF; assumption
    have U.Shape : Typ.Shape U := by
      cases ZU.WF; assumption
    exact substitutionSub_aux (Env.WellFormed.Nodup Θ.WF) U.WF U.Shape T.WF
end Typ.WellFormed
