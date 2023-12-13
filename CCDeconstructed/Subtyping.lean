import CCDeconstructed.CC
import CCDeconstructed.Var
import CCDeconstructed.Syntax
import CCDeconstructed.Classes
import CCDeconstructed.Infrastructure
import CCDeconstructed.WellFormedness
import CCDeconstructed.Subcapturing

open Feature VarCat

set_option linter.unusedVariables false

variable {i : CC}

inductive Typ.Sub : Env i → Typ i → Typ i → Prop where
  | refl_tvar {Γ : Env i} {X : Atom (.tvar i)} :
      Env.WellFormed Γ →
      Typ.WellFormed Γ X →
      Typ.Sub Γ X X
  | trans_tvar {Γ : Env i} {X : Atom (.tvar i)} {S : Typ i} :
      X <: S ∈ Γ →
      Typ.Sub Γ S T →
      Typ.Sub Γ X T
  | cap {Γ : Env i} {C₁ C₂ : Cap i} {S₁ S₂ : Typ i} :
      Typ.Sub Γ S₁ S₂ →
      Cap.Sub Γ C₁ C₂ →
      Typ.Shape S₁ →
      Typ.Shape S₂ →
      Typ.Sub Γ (.cap S₁ C₁) (.cap S₂ C₂)
  | top {Γ : Env i} {S : Typ i} :
      Env.WellFormed Γ →
      Typ.WellFormed Γ S →
      Typ.Shape S →
      Typ.Sub Γ S .top
  | arr {Γ : Env i} {S₁ S₂ : Typ i} {C₁ C₂ : Cap i} {U₁ U₂ : Typ i} (L : Finset (Atom (.var i))) :
      Typ.Sub Γ (.cap S₂ C₂) (.cap S₁ C₁) →
      (∀ x ∉ L, Typ.Sub (Γ ▷ x ⦂ .cap S₂ C₂) (Typ.instantiateRecVar U₁ 0 x) (Typ.instantiateRecVar U₂ 0 x)) →
      Typ.Sub Γ (.arr (.cap S₁ C₁) U₁) (.arr (.cap S₂ C₂) U₂)
  | all {Γ : Env i} {k : TypevarKind i} {S₁ S₂ U₁ U₂ : Typ i} (L : Finset (Atom (.tvar i))) :
      Typ.Sub Γ S₂ S₁ →
      Typ.Shape S₁ →
      Typ.Shape S₂ →
      (∀ X ∉ L, Typ.Sub (Γ ▷ X <: S₂) (Typ.instantiateRecTyp U₁ 0 X) (Typ.instantiateRecTyp U₂ 0 X)) →
      Typ.Sub Γ (.all k S₁ U₁) (.all k S₂ U₂)
  | box {Γ : Env i} {T₁ T₂ : Typ i} :
      Typ.Sub Γ T₁ T₂ ->
      Typ.Sub Γ (.box T₁) (.box T₂)

namespace Typ.Sub
  lemma regular {Γ : Env i} {T U : Typ i} :
    Sub Γ T U →
    Env.WellFormed Γ ∧ WellFormed Γ T ∧ WellFormed Γ U
  := by
    intros Sub
    induction Sub
    · case refl_tvar Γ X Γ.WF IH =>
      exact ⟨Γ.WF, ⟨IH, IH⟩⟩
    · case trans_tvar X S Γ T X.Mem Sub IH =>
      obtain ⟨Γ.WF, ⟨S.WF, T.WF⟩⟩ := IH
      exact ⟨Γ.WF, ⟨.var (Or.inl X.Mem), T.WF⟩⟩
    · case cap Γ C₁ C₂ S₁ S₂ S.Sub C.Sub S₁.Shape S₂.Shape IH =>
      obtain ⟨Γ.WF, ⟨S₁.WF, S₂.WF⟩⟩ := IH
      obtain ⟨_, ⟨C₁.WF, C₂.WF⟩⟩ := Cap.Sub.regular C.Sub
      exact ⟨Γ.WF, ⟨.cap S₁.WF S₁.Shape C₁.WF, .cap S₂.WF S₂.Shape C₂.WF⟩⟩
    · case top Γ S Γ.WF S.WF S.Shape =>
      exact  ⟨Γ.WF, ⟨S.WF, .top⟩⟩
    · case arr Γ S₁ S₂ C₁ C₂ U₁ U₂ L SC.Sub U.Sub SC.IH U.IH =>
      obtain ⟨Γ.WF, ⟨SC₂.WF, SC₁.WF⟩⟩ := SC.IH
      obtain ⟨S₁.Shape, S₁.WF, C₁.WF⟩ := SC₁.WF
      obtain ⟨S₂.Shape, S₂.WF, C₂.WF⟩ := SC₂.WF
      apply And.intro Γ.WF
      apply And.intro
      all_goals {
        apply Typ.WellFormed.arr L <;> try { assumption }
        intros x x.Fresh
        obtain ⟨_, ⟨U₁.WF, U₂.WF⟩⟩ := U.IH x x.Fresh
        rw [<- Env.concat_nil (Γ := Γ ▷ _)]
        apply Typ.WellFormed.ignore_bindings
        assumption
      }
    · case all Γ k S₁ S₂ U₁ U₂ L S.Sub S₁.Shape S₂.Shape U.Sub S.IH U.IH =>
      obtain ⟨Γ.WF, ⟨S₂.WF, S₁.WF⟩⟩ := S.IH
      apply And.intro Γ.WF
      apply And.intro
      all_goals {
        apply Typ.WellFormed.all L (by assumption) (by assumption)
        intros x x.Fresh
        obtain ⟨_, ⟨U₁.WF, U₂.WF⟩⟩ := U.IH x x.Fresh
        rw [<- Env.concat_nil (Γ := Γ ▷ _)]
        apply Typ.WellFormed.ignore_bindings
        assumption
      }
    · case box Γ T₁ T₂ Sub IH =>
      obtain ⟨Γ.WF, ⟨T₁.WF, T₂.WF⟩⟩ := IH
      exact ⟨Γ.WF, ⟨Typ.WellFormed.box T₁.WF, Typ.WellFormed.box T₂.WF⟩⟩

  lemma weaken {Γ Θ Δ : Env i} :
    Sub (Γ ++ Δ) T U →
    Env.WellFormed (Γ ++ Θ ++ Δ) →
    Sub (Γ ++ Θ ++ Δ) T U
  := by
    intros Sub ΓΘΔ.WF
    have ΓΘΔ.Nodup : Env.Nodup (Γ ++ Θ ++ Δ) :=
      Env.WellFormed.Nodup ΓΘΔ.WF
    generalize Eq.gen : Γ ++ Δ = ΓΔ at Sub
    induction Sub generalizing Δ <;> cases Eq.gen
    · case refl_tvar X ΓΔ.WF X.WF =>
      exact refl_tvar ΓΘΔ.WF (Typ.WellFormed.weaken X.WF ΓΘΔ.Nodup)
    · case trans_tvar X S T X.Mem Sub IH =>
      apply trans_tvar _ (IH ΓΘΔ.WF ΓΘΔ.Nodup rfl)
      simp at X.Mem
      simp
      cases X.Mem
      · case inl X.Mem =>
        exact Or.inl (Or.inl X.Mem)
      · case inr X.Mem =>
        exact Or.inr X.Mem
    · case cap C₁ C₂ S₁ S₂ S₁.Shape S₂.Shape S.Sub C.Sub IH =>
      exact cap (IH ΓΘΔ.WF ΓΘΔ.Nodup rfl) (Cap.Sub.weaken C.Sub ΓΘΔ.WF) S₁.Shape S₂.Shape
    · case top S S.Shape ΓΔ.WF S.WF =>
      exact top ΓΘΔ.WF (Typ.WellFormed.weaken S.WF ΓΘΔ.Nodup) S.Shape
    · case arr S₁ S₂ C₁ C₂ U₁ U₂ L SC.Sub U.Sub SC.IH U.IH =>
      apply arr (L ∪ Env.dom Γ ∪ Env.dom Θ ∪ Env.dom Δ) (SC.IH ΓΘΔ.WF ΓΘΔ.Nodup rfl)
      intros x x.Fresh
      rw [<- Env.concat_cons]
      apply U.IH x _ _ _ (by rw [Env.concat_cons])
      · clear * - x.Fresh
        aesop
      · rw [Env.concat_cons]
        apply Env.WellFormed.cons ΓΘΔ.WF
        · clear * - x.Fresh
          simp only [Assoc.val]
          aesop
        · have S₂C₂.WF : Typ.WellFormed (Γ ++ Δ) (.cap S₂ C₂) :=
            (regular SC.Sub).2.1
          rcases S₂C₂.WF
          rename_i S₂.Shape S₂.WF C₂.WF
          apply Assoc.WellFormed.val
          · exact Typ.WellFormed.weaken S₂.WF ΓΘΔ.Nodup
          · exact S₂.Shape
          · exact Cap.WellFormed.weaken C₂.WF ΓΘΔ.Nodup
      · rw [Env.concat_cons]
        apply Env.Nodup.cons ΓΘΔ.Nodup
        clear * - x.Fresh
        simp only [Assoc.val]
        aesop
    · case all k S₁ S₂ U₁ U₂ L S₁.Shape S₂.Shape S.Sub U.Sub S.IH U.IH =>
      apply all (L ∪ Env.dom Γ ∪ Env.dom Θ ∪ Env.dom Δ) (S.IH ΓΘΔ.WF ΓΘΔ.Nodup rfl) S₁.Shape S₂.Shape
      intros x x.Fresh
      rw [<- Env.concat_cons]
      apply U.IH x _ _ _ (by rw [Env.concat_cons])
      · clear * - x.Fresh
        aesop
      · rw [Env.concat_cons]
        apply Env.WellFormed.cons ΓΘΔ.WF
        · clear * - x.Fresh
          simp only [Assoc.sub]
          aesop
        · have S₂.WF : Typ.WellFormed (Γ ++ Δ) S₂ :=
            (regular S.Sub).2.1
          apply Assoc.WellFormed.sub _ S₂.Shape
          exact Typ.WellFormed.weaken S₂.WF ΓΘΔ.Nodup
      · rw [Env.concat_cons]
        apply Env.Nodup.cons ΓΘΔ.Nodup
        clear * - x.Fresh
        simp only [Assoc.sub]
        aesop
    · case box T₁ T₂ Sub IH =>
      apply box
      exact IH ΓΘΔ.WF ΓΘΔ.Nodup rfl

  @[aesop unsafe]
  lemma weaken_head {Γ Δ : Env i} :
    Sub Γ C D →
    Env.WellFormed (Γ ++ Δ) →
    Sub (Γ ++ Δ) C D
  := by
    intros Sub Nodup
    conv in Γ ++ Δ =>
      rw [<- Env.concat_nil (Γ := Γ ++ Δ)]
      rfl
    apply weaken
      <;> assumption

  @[aesop unsafe]
  lemma weaken_cons {Γ : Env i} {a : Assoc i} :
    Sub Γ C D →
    Assoc.WellFormed Γ a →
    a.name ∉ Env.dom Γ →
    Sub (Γ ▷ a) C D
  := by
    intros Sub a.WF a.NotIn
    rw [<- Env.concat_singleton]
    apply weaken_head Sub
    obtain ⟨Γ.WF, _⟩ := regular Sub
    exact Env.WellFormed.cons Γ.WF a.NotIn a.WF

  @[aesop unsafe]
  lemma Shape_iff {Γ : Env i} {S₁ S₂ : Typ i} (Sub : Sub Γ S₁ S₂) :
    Typ.Shape S₁ ↔ Typ.Shape S₂
  := by
    induction Sub
    · case refl_tvar Γ X Γ.WF X.WF =>
      simp
    · case trans_tvar S₂ Γ X S₁ X.Mem Sub IH =>
      have Γ.WF : Env.WellFormed Γ :=
        (regular Sub).1
      have XS₁.WF : Assoc.WellFormed Γ (X <: S₁) :=
        Env.WellFormed.mem Γ.WF X.Mem
      have S₁.Shape : Typ.Shape S₁ := by
        cases XS₁.WF; assumption
      simp [S₁.Shape] at IH
      simp [IH]
      apply Typ.Shape.var
      simp [Var.WellScoped]
    · case cap Γ C₁ C₂ S₁ S₂ S.Sub C.Sub S₁.Shape S₂.Shape IH =>
      clear * -
      apply Iff.intro
        <;> intros SC.Shape
        <;> cases SC.Shape
    · case top Γ S₁ Γ.WF S₁.WF S₁.Shape =>
      simp [S₁.Shape]
      apply Typ.Shape.top
    · case arr Γ S₁ S₂ C₁ C₂ U₁ U₂ L SC.Sub U.Sub SC.IH U.IH =>
      obtain ⟨Γ.WF, ⟨SC₂.WF, SC₁.WF⟩⟩ := regular SC.Sub
      have SC₁.Type : Typ.Type (.cap S₁ C₁) :=
        Typ.WellFormed.toType SC₁.WF
      have SC₂.Type : Typ.Type (.cap S₂ C₂) :=
        Typ.WellFormed.toType SC₂.WF
      rcases SC₁.Type with ⟨⟨⟩⟩ | ⟨S₁.Shape, C₁.WS⟩
      rcases SC₂.Type with ⟨⟨⟩⟩ | ⟨S₂.Shape, C₂.WS⟩
      have U.Type : ∀ x ∉ L, Typ.Type (instantiateRecVar U₁ 0 x) ∧ Typ.Type (instantiateRecVar U₂ 0 x) := by
        intros x x.Fresh
        obtain ⟨ΓxSC₂.WF, ⟨U₁.WF, U₂.WF⟩⟩ := regular (U.Sub x x.Fresh)
        apply And.intro <;> apply Typ.WellFormed.toType <;> assumption
      have SCU₁.Shape : Typ.Shape (.arr (.cap S₁ C₁) U₁) := by
        apply Typ.Shape.arr L S₁.Shape C₁.WS
        intros x x.Fresh
        exact (U.Type x x.Fresh).1
      have SCU₂.Shape : Typ.Shape (.arr (.cap S₂ C₂) U₂) := by
        apply Typ.Shape.arr L S₂.Shape C₂.WS
        intros x x.Fresh
        exact (U.Type x x.Fresh).2
      simp [SCU₁.Shape,SCU₂.Shape]
    · case all Γ k S₁ S₂ U₁ U₂ L S.Sub S₁.Shape S₂.Shape U.Sub S.IH U.IH =>
      have U.Type : ∀ X ∉ L, Typ.Type (instantiateRecTyp U₁ 0 X) ∧ Typ.Type (instantiateRecTyp U₂ 0 X) := by
        intros X X.Fresh
        obtain ⟨ΓXS₂.WF, ⟨U₁.WF, U₂.WF⟩⟩ := regular (U.Sub X X.Fresh)
        apply And.intro <;> apply Typ.WellFormed.toType <;> assumption
      have kSU₁.Shape : Typ.Shape (.all k S₁ U₁) := by
        apply Typ.Shape.all L S₁.Shape
        intros X X.Fresh
        exact (U.Type X X.Fresh).1
      have kSU₂.Shape : Typ.Shape (.all k S₂ U₂) := by
        apply Typ.Shape.all L S₂.Shape
        intros X X.Fresh
        exact (U.Type X X.Fresh).2
      simp [kSU₁.Shape,kSU₂.Shape]
    · case box Γ T₁ T₂ Sub IH =>
      obtain ⟨Γ.WF, ⟨T₁.WF, T₂.WF⟩⟩ := regular Sub
      have bT₁.Shape : Typ.Shape (.box T₁) :=
        Typ.Shape.box (Typ.WellFormed.toType T₁.WF)
      have bT₂.Shape : Typ.Shape (.box T₂) :=
        Typ.Shape.box (Typ.WellFormed.toType T₂.WF)
      simp [bT₁.Shape,bT₂.Shape]

  @[aesop safe]
  lemma reflexivity {Γ : Env i} {T : Typ i} :
    Env.WellFormed Γ →
    WellFormed Γ T →
    Sub Γ T T
  := by
    intros Γ.WF T.WF
    induction T.WF
    · case var X T U X.Mem =>
      exact refl_tvar Γ.WF (Typ.WellFormed.var X.Mem)
    · case top Γ =>
      exact top Γ.WF Typ.WellFormed.top Shape.top
    · case arr Γ S C U L S.WF S.Shape C.WF U.WF S.IH U.IH =>
      apply arr (L ∪ Env.dom Γ)
      · exact cap (S.IH Γ.WF) (Cap.Sub.reflexivity Γ.WF C.WF) S.Shape S.Shape
      · intros x x.Fresh
        apply U.IH x (by aesop)
        apply Env.WellFormed.cons Γ.WF (by aesop)
        apply Assoc.WellFormed.val <;> assumption
    · case all Γ k S U L S.WF S.Shape U.WF S.IH U.IH =>
      apply all (L ∪ Env.dom Γ) _ S.Shape S.Shape
      · intros X X.Fresh
        apply U.IH X (by aesop)
        apply Env.WellFormed.cons Γ.WF (by aesop)
        exact Assoc.WellFormed.sub S.WF S.Shape
      · exact (S.IH Γ.WF)
    · case box Γ T _ T.WF T.IH =>
      exact box (T.IH Γ.WF)
    · case cap Γ S C S.WF S.Shape C.WF S.IH =>
      exact cap (S.IH Γ.WF) (Cap.Sub.reflexivity Γ.WF C.WF) S.Shape S.Shape

  private abbrev TransitivityOn (T₂ : Typ i) :=
    ∀ {Γ : Env i} {T₁ T₃ : Typ i},
      Sub Γ T₁ T₂ →
      Sub Γ T₂ T₃ →
      Sub Γ T₁ T₃

  @[aesop unsafe]
  lemma _root_.Cap.Sub.narrowing_val {Γ : Env i} {S₁ S₂ : Typ i} {C₁ C₂ : Cap i} {D₁ D₂ : Cap i} {Z : Atom (.var i)} :
    Sub Γ (.cap S₁ C₁) (.cap S₂ C₂) ->
    Cap.Sub (Γ ▷ z ⦂ .cap S₂ C₂ ++ Δ) D₁ D₂ ->
    Cap.Sub (Γ ▷ z ⦂ .cap S₁ C₁ ++ Δ) D₁ D₂
  := by
    intros SC.Sub D.Sub

    have ΓSC₂Δ.WF : Env.WellFormed (Γ ▷ z ⦂ .cap S₂ C₂ ++ Δ) :=
      (Cap.Sub.regular D.Sub).1
    have ΓSC₁Δ.WF : Env.WellFormed (Γ ▷ z ⦂ .cap S₁ C₁ ++ Δ) := by
      apply Env.WellFormed.ignore_bindings _ ΓSC₂Δ.WF
      cases SC.Sub
      case cap S₁.Shape S₂.Shape S.Sub C.Sub =>
      obtain ⟨Γ.WF, ⟨S₁.WF, S₂.WF⟩⟩ := regular S.Sub
      obtain ⟨Γ.WF, ⟨C₁.WF, C₂.WF⟩⟩ := Cap.Sub.regular C.Sub
      apply Assoc.WellFormed.val S₁.WF S₁.Shape C₁.WF
    clear ΓSC₂Δ.WF

    generalize Eq.gen : Γ ▷ z ⦂ .cap S₂ C₂ ++ Δ = ΓSC₂Δ at D.Sub
    induction D.Sub <;> cases Eq.gen
    · case elem D₂ v v.In ΓSC₂Δ.WF D₂.WF =>
      exact Cap.Sub.elem ΓSC₁Δ.WF (Cap.WellFormed.ignore_bindings D₂.WF) v.In
    · case set D₁ D₂ Elem ΓSC₂Δ.WF D₂.WF IH =>
      apply Cap.Sub.set ΓSC₁Δ.WF (Cap.WellFormed.ignore_bindings D₂.WF) Elem
    · case var R₁ D₁ D₂ x IH x.Mem D.Sub =>
      simp at x.Mem
      rcases x.Mem with ⟨⟨x.Mem⟩ | ⟨x.Eq⟩⟩ | ⟨x.Mem⟩
      · apply Cap.Sub.var
        · simp
          exact Or.inl (Or.inl x.Mem)
        · exact IH
      · rcases x.Eq with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
        apply Cap.Sub.var (S := S₁) (C := C₁)
        · aesop
        · cases SC.Sub
          case cap S₁.Shape S₂.Shape S.Sub C.Sub =>
          apply Cap.Sub.transitivity C₂
          · rw [<- Env.concat_singleton,Env.concat_assoc]
            apply Cap.Sub.weaken_head C.Sub
            rw [<- Env.concat_assoc, Env.concat_singleton]
            exact ΓSC₁Δ.WF
          · apply IH
      · apply Cap.Sub.var (S := R₁) (C := D₁)
        · simp
          exact Or.inr x.Mem
        · exact IH

  @[aesop unsafe]
  lemma narrowing_val {Γ : Env i} {S₁ S₂ : Typ i} {C₁ C₂ : Cap i} {T₁ T₂ : Typ i} {z : Atom (.var i)} :
    Sub Γ (.cap S₁ C₁) (.cap S₂ C₂) ->
    Sub (Γ ▷ z ⦂ .cap S₂ C₂ ++ Δ) T₁ T₂ ->
    Sub (Γ ▷ z ⦂ .cap S₁ C₁ ++ Δ) T₁ T₂
  := by
    intros SC.Sub T.Sub

    have ΓSC₂Δ.WF : Env.WellFormed (Γ ▷ z ⦂ .cap S₂ C₂ ++ Δ) :=
      (regular T.Sub).1
    have ΓSC₁Δ.WF : Env.WellFormed (Γ ▷ z ⦂ .cap S₁ C₁ ++ Δ) := by
      apply Env.WellFormed.ignore_bindings _ ΓSC₂Δ.WF
      cases SC.Sub
      case cap S₁.Shape S₂.Shape S.Sub C.Sub =>
      obtain ⟨Γ.WF, ⟨S₁.WF, S₂.WF⟩⟩ := regular S.Sub
      obtain ⟨Γ.WF, ⟨C₁.WF, C₂.WF⟩⟩ := Cap.Sub.regular C.Sub
      apply Assoc.WellFormed.val S₁.WF S₁.Shape C₁.WF
    clear ΓSC₂Δ.WF

    generalize Eq.gen : Γ ▷ z ⦂ .cap S₂ C₂ ++ Δ = ΓSC₂Δ at T.Sub
    induction T.Sub generalizing Δ <;> cases Eq.gen
    · case refl_tvar X ΓS₂Δ.WF X.WF =>
      apply refl_tvar ΓSC₁Δ.WF
      apply Typ.WellFormed.ignore_bindings X.WF
    · case trans_tvar R₂ X R₁ X.Mem R.Sub IH =>
      simp at X.Mem
      rcases X.Mem with ⟨X.Mem⟩ | ⟨X.Mem⟩
      · apply trans_tvar (S := R₁)
        · simp
          exact Or.inl X.Mem
        · exact IH ΓSC₁Δ.WF rfl
      · apply trans_tvar (S := R₁)
        · simp
          exact Or.inr X.Mem
        · exact IH ΓSC₁Δ.WF rfl
    · case cap C₁ C₂ R₁ R₂ R₁.Shape R₂.Shape R.Sub C.Sub IH =>
      apply cap (IH ΓSC₁Δ.WF rfl)
      · apply Cap.Sub.narrowing_val
        · exact z
        · exact SC.Sub
        · exact C.Sub
      · exact R₁.Shape
      · exact R₂.Shape
    · case top R R.Shape ΓS₂Δ.WF R.WF =>
      apply top ΓSC₁Δ.WF
      · exact Typ.WellFormed.ignore_bindings R.WF
      · exact R.Shape
    · case arr R₁ R₂ C₁ C₂ U₁ U₂ L RC.Sub U.Sub RC.IH U.IH =>
      apply arr (L ∪ Env.dom Γ ∪ {z} ∪ Env.dom Δ)
      · exact RC.IH ΓSC₁Δ.WF rfl
      · intros x x.Fresh
        rw [<- Env.concat_cons]
        apply U.IH x
        · clear * - x.Fresh
          aesop
        · rw [Env.concat_cons]
          apply Env.WellFormed.cons ΓSC₁Δ.WF
          · clear * - x.Fresh
            simp at x.Fresh
            simp [Assoc.dom]
            aesop
          · obtain ⟨_, ⟨RC₂.WF, RC₁.WF⟩⟩ := regular RC.Sub
            cases RC₂.WF
            apply Assoc.WellFormed.val
            · apply Typ.WellFormed.ignore_bindings
              assumption
            · assumption
            · apply Cap.WellFormed.ignore_bindings
              assumption
        · rfl
    · case all k R₁ R₂ U₁ U₂ L R₁.Shape R₂.Shape R.Sub U.Sub R.IH U.IH =>
      apply all (L ∪ Env.dom Γ ∪ Env.dom Δ)
      · exact R.IH ΓSC₁Δ.WF rfl
      · exact R₁.Shape
      · exact R₂.Shape
      · intros X X.Fresh
        rw [<- Env.concat_cons]
        apply U.IH X
        · clear * - X.Fresh
          aesop
        · rw [Env.concat_cons]
          apply Env.WellFormed.cons ΓSC₁Δ.WF
          · clear * - X.Fresh
            simp at X.Fresh
            simp [Assoc.dom]
            aesop
          · obtain ⟨_, ⟨R₂.WF, R₁.WF⟩⟩ := regular R.Sub
            apply Assoc.WellFormed.sub
            · apply Typ.WellFormed.ignore_bindings
              assumption
            · assumption
        · rfl
    · case box T₁ T₂ T.Sub T.IH =>
      apply box
      apply T.IH ΓSC₁Δ.WF rfl

  @[aesop unsafe]
  private lemma narrowing_sub_aux {Γ : Env i} {S₁ S₂ T₁ T₂ : Typ i} {Z : Atom (.tvar i)} :
    TransitivityOn S₂ ->
    Sub Γ S₁ S₂ ->
    Sub (Γ ▷ Z <: S₂ ++ Δ) T₁ T₂ ->
    Sub (Γ ▷ Z <: S₁ ++ Δ) T₁ T₂
  := by
    intros Trans S.Sub T.Sub

    have ΓS₂Δ.WF : Env.WellFormed (Γ ▷ Z <: S₂ ++ Δ) :=
      (regular T.Sub).1
    have ZS₂.WF : Assoc.WellFormed (Γ ▷ Z <: S₂ ++ Δ) (Z <: S₂) :=
      Env.WellFormed.mem ΓS₂Δ.WF (by simp)
    have S₂.Shape : Typ.Shape S₂ := by
      cases ZS₂.WF; assumption
    have S₁.Shape : Typ.Shape S₁ :=
      (Shape_iff S.Sub).mpr S₂.Shape
    have ΓS₁Δ.WF : Env.WellFormed (Γ ▷ Z <: S₁ ++ Δ) := by
      apply Env.WellFormed.ignore_bindings _ ΓS₂Δ.WF
      apply Assoc.WellFormed.sub (regular S.Sub).2.1 S₁.Shape
    clear ΓS₂Δ.WF ZS₂.WF S₂.Shape S₁.Shape

    generalize Eq.gen : Γ ▷ Z <: S₂ ++ Δ = ΓS₂Δ at T.Sub
    induction T.Sub generalizing Δ <;> cases Eq.gen
    · case refl_tvar X ΓS₂Δ.WF X.WF =>
      apply refl_tvar ΓS₁Δ.WF
      apply Typ.WellFormed.ignore_bindings X.WF
    · case trans_tvar R₂ X R₁ X.Mem R.Sub IH =>
      simp at X.Mem
      rcases X.Mem with ⟨⟨X.Mem⟩ | ⟨⟨⟩, ⟨⟩⟩⟩ | ⟨X.Mem⟩
      · apply trans_tvar (S := R₁)
        · simp
          exact Or.inl (Or.inl X.Mem)
        · apply IH ΓS₁Δ.WF rfl
      · apply trans_tvar (S := S₁) (by simp)
        apply Trans
        · conv in Γ ▷ Z <: S₁ ++ Δ =>
            rw [<- Env.concat_singleton]
            rw [Env.concat_assoc]
            rw [<- Env.concat_nil (Γ := Γ ++ (∅ ▷ Z <: S₁ ++ Δ))]
            rfl
          apply weaken
          · simp; exact S.Sub
          · rw [<- Env.concat_assoc]
            rw [Env.concat_singleton]
            rw [Env.concat_nil]
            exact ΓS₁Δ.WF
        · apply IH ΓS₁Δ.WF rfl
      · apply trans_tvar (S := R₁)
        · simp; apply Or.inr X.Mem
        · apply IH ΓS₁Δ.WF rfl
    · case cap C₁ C₂ R₁ R₂ R₁.Shape R₂.Shape R.Sub C.Sub IH =>
      apply cap (IH ΓS₁Δ.WF rfl)
      · apply Cap.Sub.ignore_sub_bindings ΓS₁Δ.WF C.Sub
      · exact R₁.Shape
      · exact R₂.Shape
    · case top R R.Shape ΓS₂Δ.WF R.WF =>
      apply top ΓS₁Δ.WF
      · exact Typ.WellFormed.ignore_bindings R.WF
      · exact R.Shape
    · case arr R₁ R₂ C₁ C₂ U₁ U₂ L RC.Sub U.Sub RC.IH U.IH =>
      apply arr (L ∪ Env.dom Γ ∪ Env.dom Δ)
      · exact RC.IH ΓS₁Δ.WF rfl
      · intros x x.Fresh
        rw [<- Env.concat_cons]
        apply U.IH x
        · clear * - x.Fresh
          aesop
        · rw [Env.concat_cons]
          apply Env.WellFormed.cons ΓS₁Δ.WF
          · clear * - x.Fresh
            simp at x.Fresh
            simp [Assoc.dom]
            aesop
          · obtain ⟨_, ⟨RC₂.WF, RC₁.WF⟩⟩ := regular RC.Sub
            cases RC₂.WF
            apply Assoc.WellFormed.val
            · apply Typ.WellFormed.ignore_bindings
              assumption
            · assumption
            · apply Cap.WellFormed.ignore_bindings
              assumption
        · rfl
    · case all k R₁ R₂ U₁ U₂ L R₁.Shape R₂.Shape R.Sub U.Sub R.IH U.IH =>
      apply all (L ∪ Env.dom Γ ∪ {Z} ∪ Env.dom Δ)
      · exact R.IH ΓS₁Δ.WF rfl
      · exact R₁.Shape
      · exact R₂.Shape
      · intros X X.Fresh
        rw [<- Env.concat_cons]
        apply U.IH X
        · clear * - X.Fresh
          aesop
        · rw [Env.concat_cons]
          apply Env.WellFormed.cons ΓS₁Δ.WF
          · clear * - X.Fresh
            simp at X.Fresh
            simp [Assoc.dom]
            aesop
          · obtain ⟨_, ⟨R₂.WF, R₁.WF⟩⟩ := regular R.Sub
            apply Assoc.WellFormed.sub
            · apply Typ.WellFormed.ignore_bindings
              assumption
            · assumption
        · rfl
    · case box T₁ T₂ T.Sub T.IH =>
      apply box
      apply T.IH ΓS₁Δ.WF rfl

  @[aesop unsafe]
  private lemma transitivity_aux {T₂ : Typ i} :
      Typ.Type T₂ →
      TransitivityOn T₂
  := by
    revert T₂
    apply Typ.Type.rec
      (motive_1 := fun (T₂ : Typ i) (Type₂ : Typ.Type T₂) => TransitivityOn T₂)
      (motive_2 := fun (S₂ : Typ i) (Shape₂ : Typ.Shape S₂) => TransitivityOn S₂)
    · case shape =>
      intros S₂ S₂.Shape IH Γ S₁ S₃ Sub₁₂ Sub₂₃
      apply IH Sub₁₂ Sub₂₃
    · case cap =>
      intros S₂ C₂ S₂.Shape C₂.WS IH Γ T₁ T₃ Sub₁₂ Sub₂₃
      cases Sub₁₂
      · case trans_tvar X S₁ X.Mem Sub₁₂ =>
        have Γ.WF : Env.WellFormed Γ :=
          (regular Sub₁₂).1
        have XS₁.WF : Assoc.WellFormed Γ (X <: S₁) :=
          Env.WellFormed.mem Γ.WF X.Mem
        have S₁.Shape : Typ.Shape S₁ := by
          cases XS₁.WF; assumption
        have SC₂.Shape : Typ.Shape (Typ.cap S₂ C₂) :=
          (Shape_iff Sub₁₂).mp S₁.Shape
        cases SC₂.Shape
      . case cap C₁ S₁ S₁.Shape S₂.Shape S.Sub₁₂ C.Sub₁₂ =>
        cases Sub₂₃
        · case cap C₃ S₃ S₂.Shape S₃.Shape S.Sub₂₃ C.Sub₂₃ =>
          exact cap (IH S.Sub₁₂ S.Sub₂₃) (Cap.Sub.transitivity C₂ C.Sub₁₂ C.Sub₂₃) S₁.Shape S₂.Shape
        · case top Γ.WF SC₂.Shape SC₂.WF =>
          cases SC₂.Shape
    · case var =>
      intros X₂ X₂.WS Γ S₁ S₃ Sub₁₂ Sub₂₃
      cases X₂ <;> simp [Var.WellScoped] at X₂.WS
      case free X₂ =>
      generalize Eq.gen : var (.free X₂) = S₂ at Sub₁₂
      induction Sub₁₂ <;> cases Eq.gen
      · case refl_tvar Γ Γ.WF X₂.WF =>
        exact Sub₂₃
      · case trans_tvar Γ Y₂ S₂ Y₂.Mem Sub₁₂ IH =>
        exact trans_tvar Y₂.Mem (IH Sub₂₃ rfl)
    · case top =>
      intros Γ S₁ S₃ Sub₁₂ Sub₂₃
      cases Sub₂₃
      case top Γ.WF top.Shape top.WF =>
      have S₁.WF : Typ.WellFormed Γ S₁ :=
        (regular Sub₁₂).2.1
      have S₁.Shape : Typ.Shape S₁ :=
        (Shape_iff Sub₁₂).mpr top.Shape
      apply top Γ.WF S₁.WF S₁.Shape
    · case arr =>
      intros S₂ C₂ U₂ L₂ S₂.Shape C₂.WS U₂.Type S₂.IH₁ U₂.IH₁ Γ S₁ S₃ Sub₁₂ Sub₂₃
      generalize Eq.gen : Typ.arr (Typ.cap S₂ C₂) U₂ = SCU₂ at Sub₁₂
      induction Sub₁₂ <;> cases Eq.gen <;> cases Sub₂₃
      · case trans_tvar.refl.top Γ X₁ S₁ X₁.Mem Sub₁₂ Γ.WF SCU₂.Shape SCU₂.WF SCU₂.IH =>
        exact top Γ.WF (WellFormed.var (Or.inl X₁.Mem)) (Typ.Shape.var (by simp [Var.WellScoped]))
      · case trans_tvar.refl.arr Γ X₁ S₁ X₁.Mem Sub₁₂ S₃ C₃ U₃ L SC.Sub U.Sub IH =>
        apply trans_tvar X₁.Mem
        apply IH <;> try { assumption }
        · exact arr L SC.Sub U.Sub
        · rfl
      · case arr.refl.top Γ S₁ C₁ U₁ L SC.Sub₂₁ U.Sub₁₂ Γ.WF SCU₂.Shape SCU₂.WF SC₂.IH₂ U₂.IH₂ =>
        obtain ⟨Γ.WF, ⟨SC₂.WF, SC₁.WF⟩⟩ := regular SC.Sub₂₁
        cases SC₁.WF
        rename_i S₁.Shape S₁.WF C₁.WF
        cases SC₂.WF
        rename_i S₂.Shape S₂.WF C₂.WF
        apply top Γ.WF
        · apply Typ.WellFormed.arr L S₁.WF S₁.Shape C₁.WF
          intros x x.Fresh
          specialize U.Sub₁₂ x x.Fresh
          conv in Γ ▷ x ⦂ Typ.cap S₁ C₁ =>
            rw [<- Env.concat_singleton]
            rw [<- Env.concat_nil (Γ := Γ ++ ∅ ▷ x ⦂ Typ.cap S₁ C₁)]
            rfl
          apply Typ.WellFormed.ignore_bindings
          exact (regular U.Sub₁₂).2.1
        · apply Typ.Shape.arr L S₁.Shape (Cap.WellFormed.toWellScoped C₁.WF)
          intros x x.Fresh
          specialize U.Sub₁₂ x x.Fresh
          apply Typ.WellFormed.toType (Γ := Γ ▷ x ⦂ Typ.cap S₂ C₂)
          exact (regular U.Sub₁₂).2.1
      · case arr.refl.arr Γ S₁ C₁ U₁ L₁₂ SC.Sub₂₁ U.Sub₁₂ S₃ C₃ U₃ L₂₃ SC.Sub₃₂ U.Sub₂₃ SC.IH₂ U₂.IH₂ =>
        apply arr (L₂ ∪ L₁₂ ∪ L₂₃)
        · cases SC.Sub₂₁
          rename_i S₂.Shape S₁.Shape S.Sub₂₁ C.Sub₂₁
          cases SC.Sub₃₂
          rename_i S₃.Shape S₂.Shape S.Sub₃₂ C.Sub₃₂
          apply cap
          · exact S₂.IH₁ S.Sub₃₂ S.Sub₂₁
          · exact Cap.Sub.transitivity _ C.Sub₃₂ C.Sub₂₁
          · exact S₃.Shape
          · exact S₁.Shape
        · intros x x.Fresh
          have x.Fresh₂  : x ∉ L₂  := by clear * - x.Fresh; aesop
          have x.Fresh₁₂ : x ∉ L₁₂ := by clear * - x.Fresh; aesop
          have x.Fresh₂₃ : x ∉ L₂₃ := by clear * - x.Fresh; aesop
          specialize U.Sub₁₂ x x.Fresh₁₂
          specialize U.Sub₂₃ x x.Fresh₂₃
          replace U.Sub₁₂ : Sub (Γ ▷ x ⦂ Typ.cap S₃ C₃)
                              (instantiateRecVar U₁ 0 x)
                              (instantiateRecVar U₂ 0 x)
          := by
            conv in Γ ▷ x ⦂ Typ.cap S₃ C₃ =>
              rw [<- Env.concat_nil (Γ := Γ ▷ x ⦂ Typ.cap S₃ C₃)]
              rfl
            apply narrowing_val SC.Sub₃₂
            rw [Env.concat_nil]
            exact U.Sub₁₂
          apply U₂.IH₁ x x.Fresh₂ U.Sub₁₂ U.Sub₂₃
    · case all =>
      intros k R₂ U₂ L₂ R₂.Shape U₂.Type R₂.IH₁ U₂.IH₁ Γ S₁ S₃ Sub₁₂ Sub₂₃
      generalize Eq.gen : Typ.all k R₂ U₂ = kRU₂ at Sub₁₂
      induction Sub₁₂ <;> cases Eq.gen <;> cases Sub₂₃
      · case trans_tvar.refl.top Γ X₁ S₁ X₁.Mem Sub₁₂ Γ.WF SCU₂.Shape SCU₂.WF SCU₂.IH =>
        exact top Γ.WF (WellFormed.var (Or.inl X₁.Mem)) (Typ.Shape.var (by simp [Var.WellScoped]))
      · case trans_tvar.refl.all Γ X₁ S₁ X₁.Mem Sub₁₂ R₃ U₃ L R₃.Shape R₂.Shape R.Sub₃₂ U.Sub₂₃ IH =>
        apply trans_tvar X₁.Mem
        apply IH <;> try { assumption }
        · apply all L R.Sub₃₂ R₂.Shape R₃.Shape U.Sub₂₃
        · rfl
      · case all.refl.top Γ R₁ U₁ L R₁.Shape R.Sub₂₁ R₂.Shape U.Sub₁₂ Γ.WF kRU₂.Shape kRU₂.WF R₂.IH₂ U₂.IH₂ =>
        obtain ⟨Γ.WF, ⟨R₂.WF, R₁.WF⟩⟩ := regular R.Sub₂₁
        apply top Γ.WF
        · apply Typ.WellFormed.all L R₁.WF R₁.Shape
          intros X X.Fresh
          specialize U.Sub₁₂ X X.Fresh
          conv in Γ ▷ X <: R₁ =>
            rw [<- Env.concat_singleton]
            rw [<- Env.concat_nil (Γ := Γ ++ ∅ ▷ X <: R₁)]
            rfl
          apply Typ.WellFormed.ignore_bindings
          exact (regular U.Sub₁₂).2.1
        · apply Typ.Shape.all L R₁.Shape
          intros X X.Fresh
          specialize U.Sub₁₂ X X.Fresh
          apply Typ.WellFormed.toType (Γ := Γ ▷ X <: R₂)
          exact (regular U.Sub₁₂).2.1
      · case all.refl.all Γ R₁ U₁ L₁₂ R₁.Shape R.Sub₂₁ R₂.Shape U.Sub₁₂ R₃ U₃ L₂₃ R₃.Shape R₂.Shape R.Sub₃₂ U.Sub₂₃ R.IH₂ U₂.IH₂ =>
        apply all (L₂ ∪ L₁₂ ∪ L₂₃)
        · exact R₂.IH₁ R.Sub₃₂ R.Sub₂₁
        · exact R₁.Shape
        · exact R₃.Shape
        · intros X X.Fresh
          have X.Fresh₂  : X ∉ L₂  := by clear * - X.Fresh; aesop
          have X.Fresh₁₂ : X ∉ L₁₂ := by clear * - X.Fresh; aesop
          have X.Fresh₂₃ : X ∉ L₂₃ := by clear * - X.Fresh; aesop
          specialize U.Sub₁₂ X X.Fresh₁₂
          specialize U.Sub₂₃ X X.Fresh₂₃
          replace U.Sub₁₂ : Sub (Γ ▷ X <: R₃)
                              (instantiateRecTyp U₁ 0 (Var.free X))
                              (instantiateRecTyp U₂ 0 (Var.free X))
          := by
            conv in Γ ▷ X <: R₃ =>
              rw [<- Env.concat_nil (Γ := Γ ▷ X <: R₃)]
              rfl
            apply narrowing_sub_aux R₂.IH₁ R.Sub₃₂
            rw [Env.concat_nil]
            exact U.Sub₁₂
          apply U₂.IH₁ X X.Fresh₂ U.Sub₁₂ U.Sub₂₃
    · case box =>
      intros T₂ _ T₂.Type T₂.IH₁ Γ S₁ S₃ Sub₁₂ Sub₂₃
      generalize Eq.gen : Typ.box T₂ = bT₂ at Sub₁₂
      induction Sub₁₂ <;> cases Eq.gen <;> cases Sub₂₃
      · case trans_tvar.refl.top Γ X R X.Mem Sub₁₂ Γ.WF bT₂.Shape bT₂.WF T.IH₂ =>
        exact top Γ.WF (Typ.WellFormed.var (Or.inl X.Mem)) (Typ.Shape.var (by simp [Var.WellScoped]))
      · case trans_tvar.refl.box Γ X R X.Mem Sub₁₂ T₃ Sub₂₃ T.IH₂ =>
        exact trans_tvar X.Mem (T.IH₂ (box Sub₂₃) rfl)
      · case box.refl.top Γ T₁ Sub₁₂ Γ.WF  bT₂.Shape bT₂.WF T.IH =>
        have T₁.WF : Typ.WellFormed Γ T₁ :=
          (regular Sub₁₂).2.1
        have bT₁.WF : Typ.WellFormed Γ (.box T₁) :=
          Typ.WellFormed.box T₁.WF
        have T₁.Type : Typ.Type T₁ :=
          Typ.WellFormed.toType T₁.WF
        have bT₁.Shape : Typ.Shape (.box T₁) :=
          Typ.Shape.box T₁.Type
        apply top Γ.WF bT₁.WF bT₁.Shape
      · case box.refl.box Γ T₁ Sub₁₂ T₃ Sub₂₃ T.IH₂ =>
        exact box (T₂.IH₁ Sub₁₂ Sub₂₃)

  @[aesop unsafe]
  lemma transitivity {Γ : Env i} {T₁ : Typ i} (T₂ : Typ i) {T₃ : Typ i} :
    Sub Γ T₁ T₂ →
    Sub Γ T₂ T₃ →
    Sub Γ T₁ T₃
  := by
    intros Sub₁₂ Sub₂₃
    have T₂.Type : Typ.Type T₂ :=
      Typ.WellFormed.toType (regular Sub₁₂).2.2
    revert Γ T₁ T₃
    exact transitivity_aux T₂.Type

  @[aesop unsafe]
  lemma narrowing_sub {Γ : Env i} {S₁ S₂ T₁ T₂ : Typ i} {Z : Atom (.tvar i)} :
    Sub Γ S₁ S₂ ->
    Sub (Γ ▷ Z <: S₂ ++ Δ) T₁ T₂ ->
    Sub (Γ ▷ Z <: S₁ ++ Δ) T₁ T₂
  := by
    apply narrowing_sub_aux
    intros Γ S₁ S₃
    apply transitivity

  namespace Inversion
    @[aesop unsafe]
    lemma cap {Γ : Env i} {S₁ : Typ i} {C₁ : Cap i} {T₂ : Typ i} :
      Sub Γ (.cap S₁ C₁) T₂ →
      ∃ S₂ C₂, T₂ = .cap S₂ C₂
             ∧ Sub Γ S₁ S₂
             ∧ Cap.Sub Γ C₁ C₂
    := by
      intros Sub
      generalize Eq.gen : Typ.cap S₁ C₁ = T₁ at Sub
      induction Sub <;> cases Eq.gen
      · case cap.refl Γ C₂ S₂ S₂.Shape S.Sub S₁.Shape IH C.Sub =>
        exists S₂, C₂
      · case top.refl Γ Γ.WF SC₁.WF SC₁.Shape =>
        cases SC₁.Shape
  end Inversion
end Typ.Sub
