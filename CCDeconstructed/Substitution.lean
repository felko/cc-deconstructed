import CCDeconstructed.CC
import CCDeconstructed.Var
import CCDeconstructed.Syntax
import CCDeconstructed.Classes
import CCDeconstructed.Infrastructure
import CCDeconstructed.WellFormedness
import CCDeconstructed.Subcapturing
import CCDeconstructed.Subtyping

set_option linter.unusedVariables false

namespace Cap.Sub
  @[aesop unsafe]
  lemma substitutionCap {Γ Δ : Env i} {z : Atom (.var i)} {S₂ : Typ i} {D₁ D₂ : Cap i} {C₁ C₂ : Cap i} :
    Sub Γ D₁ D₂ →
    Sub (Γ ▷ z ⦂ .cap S₂ D₂ ++ Δ) C₁ C₂ →
    Sub (Γ ++ Δ.substituteCap z D₁) (C₁.substituteCap z D₁) (C₂.substituteCap z D₁)
  := by
    intros D.Sub C.Sub
    obtain ⟨Γ.WF, ⟨D₁.WF, D₂.WF⟩⟩ := regular D.Sub
    obtain ⟨Θ.WF, ⟨C₁.WF, C₂.WF⟩⟩ := regular C.Sub
    induction C.Sub
    · case elem C₂ v Θ.WF C₂.WF v.In =>
      conv in substituteCap {v} z D₁ =>
        simp [substituteCap]
        rfl
      split
      · case inl v.Eq =>
        cases v.Eq
        simp
        apply set
        · exact Env.WellFormed.substitutionCap D₁.WF Θ.WF
        · exact Cap.WellFormed.substitutionCap (Env.WellFormed.Nodup Θ.WF) D₁.WF C₂.WF
        · intros w w.In
          apply elem
          · exact Env.WellFormed.substitutionCap D₁.WF Θ.WF
          · exact Cap.WellFormed.substitutionCap (Env.WellFormed.Nodup Θ.WF) D₁.WF C₂.WF
          · simp [substituteCap,v.In]
            exact Or.inr w.In
      · case inr v.Neq =>
        apply elem
        · exact Env.WellFormed.substitutionCap D₁.WF Θ.WF
        · exact Cap.WellFormed.substitutionCap (Env.WellFormed.Nodup Θ.WF) D₁.WF C₂.WF
        · simp [substituteCap]
          split
          · case a.inl z.In =>
            simp
            apply Or.inl (And.intro v.In _)
            exact v.Neq ∘ Eq.symm
          · case a.inr z.NotIn =>
            exact v.In
    · case set C₁ C₂ Θ.WF C₂.WF Elem IH =>
      conv in substituteCap C₁ z D₁ => simp [substituteCap]; rfl
      split
      · case inl z.InC₁ =>
        apply set
        · apply Env.WellFormed.substitutionCap D₁.WF Θ.WF
        · apply Cap.WellFormed.substitutionCap (Env.WellFormed.Nodup Θ.WF) D₁.WF C₂.WF
        · intros v v.In
          replace v.In : v ∈ substituteCap C₁ z D₁ := by
            simp at v.In
            simp [substituteCap,z.InC₁]
            exact v.In
          obtain ⟨w, ⟨w.InC₁, v.InW⟩⟩ := Cap.mem_substituteCap v.In
          have sw.WF : WellFormed (Γ ▷ z ⦂ .cap S₂ D₂ ++ Δ) {w} := by
            intros w' w'.Eq
            simp at w'.Eq
            cases w'.Eq
            apply C₁.WF w w.InC₁
          apply transitivity (substituteCap {w} z D₁)
          · apply elem
            · exact Env.WellFormed.substitutionCap D₁.WF Θ.WF
            · apply Cap.WellFormed.substitutionCap (Env.WellFormed.Nodup Θ.WF) D₁.WF sw.WF
            · exact v.InW
          · apply IH w w.InC₁ sw.WF C₂.WF
      · case inr z.NotInC₁ =>
        apply set
        · apply Env.WellFormed.substitutionCap D₁.WF Θ.WF
        · apply Cap.WellFormed.substitutionCap (Env.WellFormed.Nodup Θ.WF) D₁.WF C₂.WF
        · intros v v.InC₁
          rw [<- Cap.substituteCap_fresh (x := z) (D := D₁) (C := {v})]
          · obtain ⟨_, ⟨sv.WF, C₂.WF⟩⟩ := regular (Elem v v.InC₁)
            apply IH v v.InC₁ sv.WF C₂.WF
          · clear * - z.NotInC₁ v.InC₁
            aesop
    · case var S₂' D₂' C₂ x x.Mem C.Sub IH =>
      conv in substituteCap {Var.free x} z D₁ =>
        simp [substituteCap,Var.substitute]
        rfl
      split
      · case inl Eq =>
        cases Eq
        have x.Mem' : z ⦂ .cap S₂ D₂ ∈ Γ ▷ z ⦂ .cap S₂ D₂ ++ Δ := by
          clear * -
          aesop
        have Eq : Typ.cap S₂' D₂' = Typ.cap S₂ D₂ := by
          clear * - Θ.WF x.Mem x.Mem'
          simp only [Assoc.val] at x.Mem x.Mem' Θ.WF
          cases (Env.Nodup.unique (Env.WellFormed.Nodup Θ.WF) x.Mem x.Mem')
          assumption
        simp at Eq
        obtain ⟨Eq.S₂, Eq.D₂⟩ := Eq
        cases Eq.S₂
        cases Eq.D₂
        clear x.Mem x.Mem'
        simp
        apply transitivity D₂
        · rw [<- Env.concat_nil (Γ := Γ ++ Δ.substituteCap z D₁)]
          apply weaken
          · simp
            exact D.Sub
          · apply Env.WellFormed.substitutionCap D₁.WF Θ.WF
        · have Θ.Nodup : Env.Nodup (Γ ▷ z ⦂ .cap S₂ D₂ ++ Δ) :=
            Env.WellFormed.Nodup Θ.WF
          have ΓU.Nodup : Env.Nodup (Γ ▷ z ⦂ .cap S₂ D₂) :=
            Env.Nodup.left_of_concat Θ.Nodup
          have z.NotIn : z ∉ Env.dom Γ := by
            cases ΓU.Nodup
            assumption
          rw [<- Cap.substituteCap_fresh (C := D₂) (x := z) (D := D₁)]
          · apply IH
            · rw [<- Env.concat_singleton]
              rw [Env.concat_assoc]
              rw [<- Env.concat_nil (Γ := Γ ++ (∅ ▷ z ⦂ .cap S₂ D₂ ++ Δ))]
              apply Cap.WellFormed.weaken
              · simp
                exact D₂.WF
              · rw [<- Env.concat_assoc]
                simp
                apply Env.WellFormed.Nodup Θ.WF
            · exact C₂.WF
          · revert z.NotIn
            contrapose
            simp
            apply Cap.WellFormed.fv_subset_dom D₂.WF
      · case inr Neq =>
        simp [Neq] at x.Mem
        rcases x.Mem with ⟨⟨x.Mem⟩ | ⟨⟨⟩, ⟨⟩⟩⟩ | ⟨x.Mem⟩
        · obtain ⟨Γ₁, ⟨Γ₂, ⟨Eq.Γ, ⟨S₂'.WF, ⟨S₂'.Shape, ⟨D₂'.WF, x.NotIn⟩⟩⟩⟩⟩⟩ := Env.WellFormed.split_val Γ.WF x.Mem
          replace IH : Sub (Γ ++ Env.substituteCap Δ z D₁) (substituteCap D₂' z D₁) (substituteCap C₂ z D₁) := by
            apply IH
            · rw [Eq.Γ]
              conv =>
                lhs
                rw [<- Env.concat_cons]
                rw [<- Env.concat_singleton]
                rw [Env.concat_assoc,Env.concat_assoc]
                rw [<- Env.concat_nil (Γ := ∅ ▷ _ ++ _)]
                rw [<- Env.concat_assoc]
                rfl
              apply Cap.WellFormed.weaken
              · simp
                exact D₂'.WF
              · simp
                rw [<- Env.concat_assoc,<- Env.concat_assoc]
                rw [Env.concat_cons]
                simp
                rw [<- Eq.Γ]
                apply Env.WellFormed.Nodup Θ.WF
            · exact C₂.WF
          · apply var (S := S₂') (C := D₂')
            · simp
              exact Or.inl x.Mem
            · rw [<- Cap.substituteCap_fresh (C := D₂') (x := z) (D := D₁)]
              apply IH
              have Θ.Nodup : Env.Nodup (Γ ▷ z ⦂ .cap S₂ D₂ ++ Δ) :=
                Env.WellFormed.Nodup Θ.WF
              have ΓU.Nodup : Env.Nodup (Γ ▷ z ⦂ .cap S₂ D₂) :=
                Env.Nodup.left_of_concat Θ.Nodup
              have z.NotIn : z ∉ Env.dom Γ := by
                cases ΓU.Nodup
                assumption
              replace z.NotIn : z ∉ Env.dom Γ₁ := by
                rw [Eq.Γ] at z.NotIn
                simp at z.NotIn
                exact z.NotIn ∘ Or.inl
              revert z.NotIn
              contrapose
              simp
              apply Cap.WellFormed.fv_subset_dom D₂'.WF
        · simp at Neq
        · have x.MemΘ : x ⦂ .cap S₂' D₂' ∈ Γ ▷ z ⦂ .cap S₂ D₂ ++ Δ := by
            simp
            apply Or.inr x.Mem
          obtain ⟨Θ₁, ⟨Θ₂, ⟨Eq.Θ, ⟨S₂'.WF, ⟨S₂'.Shape, ⟨D₂'.WF, x.NotIn⟩⟩⟩⟩⟩⟩ :=
            Env.WellFormed.split_val Θ.WF x.MemΘ
          replace IH : Sub (Γ ++ Δ.substituteCap z D₁) (D₂'.substituteCap z D₁) (C₂.substituteCap z D₁) := by
            apply IH
            · rw [Eq.Θ]
              conv =>
                lhs
                rw [<- Env.concat_singleton]
                rw [Env.concat_assoc]
                rw [<- Env.concat_nil (Γ := ∅ ▷ _ ++ _)]
                rw [<- Env.concat_assoc]
                rfl
              apply Cap.WellFormed.weaken
              · simp
                exact D₂'.WF
              · simp
                rw [<- Env.concat_assoc]
                rw [Env.concat_cons]
                simp
                rw [<- Eq.Θ]
                apply Env.WellFormed.Nodup Θ.WF
            · exact C₂.WF
          apply var (S := Typ.substituteCap S₂' z D₁) (C := Cap.substituteCap D₂' z D₁)
          · simp
            apply Or.inr
            exists x ⦂ .cap S₂' D₂'
          · apply IH

  @[aesop unsafe]
  lemma substitutionVal {Γ Δ : Env i} {z : Atom (.var i)} {u : Var (.var i)} {S : Typ i} {D : Cap i} {C₁ C₂ : Cap i} :
    Sub Γ {u} D →
    Sub (Γ ▷ z ⦂ .cap S D ++ Δ) C₁ C₂ →
    Sub (Γ ++ Δ.substituteVar z u) (C₁.substituteVar z u) (C₂.substituteVar z u)
  := substitutionCap

  @[aesop unsafe]
  lemma substitutionSub {Γ Δ : Env i} {Z : Atom (.tvar i)} {U : Typ i} {C₁ C₂ : Cap i} :
    Cap.Sub (Γ ▷ Z <: U ++ Δ) C₁ C₂ →
    Cap.Sub (Γ ++ Env.substituteTyp Δ Z U) C₁ C₂
  := by
    intros C.Sub
    obtain ⟨Θ.WF, ⟨C₁.WF, C₂.WF⟩⟩ := regular C.Sub
    obtain ⟨U.WF, ⟨U.Shape, Z.NotIn⟩⟩ := Env.WellFormed.inversion_sub Θ.WF
    induction C.Sub
    · case elem C₂ v Θ.WF C₂.WF v.In =>
      apply elem
      · exact Env.WellFormed.substitutionSub Θ.WF
      · exact Cap.WellFormed.substitutionSub U.WF C₂.WF
      · exact v.In
    · case set C₁ C₂ Θ.WF C₂.WF Elem IH =>
      apply set
      · exact Env.WellFormed.substitutionSub Θ.WF
      · exact Cap.WellFormed.substitutionSub U.WF C₂.WF
      · intros v v.InC₁
        obtain ⟨_, ⟨sv.WF, C₂.WF⟩⟩ := (Elem v v.InC₁).regular
        apply IH v v.InC₁ sv.WF C₂.WF
    · case var S₂ D₂ C₂ x x.Mem C.Sub IH =>
      simp at x.Mem
      rcases x.Mem with ⟨x.Mem⟩ | ⟨x.Mem⟩
      · apply var (S := S₂) (C := D₂)
        · simp
          exact Or.inl x.Mem
        · obtain ⟨_, ⟨D₂.WF, C₂.WF⟩⟩ := regular C.Sub
          apply IH D₂.WF C₂.WF
      · apply var (S := Typ.substituteTyp S₂ Z U) (C := D₂)
        · simp
          apply Or.inr
          exists x ⦂ .cap S₂ D₂
        · obtain ⟨_, ⟨D₂.WF, C₂.WF⟩⟩ := regular C.Sub
          apply IH D₂.WF C₂.WF
end Cap.Sub

namespace Typ.Sub
  @[aesop unsafe]
  lemma substitutionVar {Γ Δ : Env i} {z : Atom (.var i)} {u : Var (.var i)} {S : Typ i} {C : Cap i} {T₁ T₂ : Typ i} :
    Cap.Sub Γ {u} C →
    Sub (Γ ▷ z ⦂ .cap S C ++ Δ) T₁ T₂ →
    Sub (Γ ++ Δ.substituteVar z u) (T₁.substituteVar z u) (T₂.substituteVar z u)
  := by
    intros u.Sub T.Sub
    have Θ.WF := (regular T.Sub).1
    obtain ⟨Γ.WF, ⟨u.WF, C.WF⟩⟩ := Cap.Sub.regular u.Sub
    simp [Cap.WellFormed] at u.WF
    have u.WS : Var.WellScoped (allowCap := true) u :=
      Var.WellFormed.toWellScoped u.WF
    generalize Eq.gen : Γ ▷ z ⦂ .cap S C ++ Δ = Θ at T.Sub
    induction T.Sub generalizing Δ <;> cases Eq.gen <;> simp
    · case refl_tvar.refl X Θ.WF X.WF =>
      apply refl_tvar
      · exact Env.WellFormed.substitutionVal u.WF Θ.WF
      · exact Typ.WellFormed.substitutionVal Θ.WF u.WF X.WF
    · case trans_tvar.refl U₂ X U₁ X.Mem U.Sub IH =>
      have Γ.WF : Env.WellFormed Γ := by
        cases (Env.WellFormed.concat_left Θ.WF)
        assumption
      simp at X.Mem
      rcases X.Mem with ⟨X.Mem⟩ | ⟨X.Mem⟩
      · apply trans_tvar (S := U₁)
        · simp
          exact Or.inl X.Mem
        · rw [<- Typ.substituteVar_fresh (T := U₁) (x := z) (u := u)]
          · apply IH Θ.WF rfl
          · have Θ.Nodup : Env.Nodup (Γ ▷ z ⦂ .cap S C ++ Δ) :=
              Env.WellFormed.Nodup Θ.WF
            have ΓSC.Nodup : Env.Nodup (Γ ▷ z ⦂ .cap S C) :=
              Env.Nodup.left_of_concat Θ.Nodup
            have z.NotIn : z ∉ Env.dom Γ := by
              cases ΓSC.Nodup
              assumption
            revert z.NotIn
            contrapose
            simp
            apply Typ.WellFormed.fvVar_subset_dom
            obtain ⟨Γ₁, ⟨Γ₂, ⟨Γ.Eq, ⟨U₁.WF, ⟨U₁.Shape, X.NotIn⟩⟩⟩⟩⟩ := Env.WellFormed.split_sub Γ.WF X.Mem
            rw [Γ.Eq]
            rw [<- Env.concat_singleton]
            rw [Env.concat_assoc]
            rw [<- Env.concat_nil (Γ := ∅ ▷ X <: U₁ ++ Γ₂)]
            rw [<- Env.concat_assoc]
            apply Typ.WellFormed.weaken
            · simp
              exact U₁.WF
            · rw [<- Env.concat_assoc]
              simp [Env.concat_singleton]
              rw [<- Γ.Eq]
              exact Env.WellFormed.Nodup Γ.WF
      · apply trans_tvar (S := substituteVar U₁ z u)
        · simp
          apply Or.inr
          exists X <: U₁
        · exact IH Θ.WF rfl
    · case cap.refl C₁ C₂ S₁ S₂ S₁.Shape S₂.Shape S.Sub C.Sub S.IH =>
      apply cap
      · exact S.IH Θ.WF rfl
      · exact Cap.Sub.substitutionVal u.Sub C.Sub
      · exact Shape_substituteVar u.WS S₁.Shape
      · exact Shape_substituteVar u.WS S₂.Shape
    · case top.refl S S.Shape Θ.WF S.WF =>
      apply top
      · exact Env.WellFormed.substitutionVal u.WF Θ.WF
      · exact Typ.WellFormed.substitutionVal Θ.WF u.WF S.WF
      · exact Shape_substituteVar u.WS S.Shape
    · case arr.refl S₁ S₂ C₁ C₂ U₁ U₂ L SC.Sub U.Sub SC.IH U.IH =>
      apply arr (L ∪ Env.dom Γ ∪ {z} ∪ Env.dom Δ)
      · exact SC.IH Θ.WF rfl
      · intros x x.Fresh
        rw [
          <- Var.substitute_fresh (v := .free x) (x := z) (u := u) (by clear * - x.Fresh; simp; aesop),
          <- substituteVar_instantiateRecVar u.WS,
          <- substituteVar_instantiateRecVar u.WS
        ]
        conv in (_ ▷ _) =>
          rw [<- Env.concat_cons]
          rhs
          change Env.substituteVar (Δ ▷ x ⦂ .cap S₂ C₂) z u
          rfl
        apply U.IH x (by clear * - x.Fresh; aesop)
        · rw [Env.concat_cons]
          apply Env.WellFormed.cons Θ.WF
          · clear * - x.Fresh
            simp [Assoc.dom]
            aesop
          · have SC₂.WF : Typ.WellFormed (Γ ▷ z ⦂ .cap S C ++ Δ) (.cap S₂ C₂) :=
              (regular SC.Sub).2.1
            cases SC₂.WF
            rename_i S₂.WF S₂.Shape C₂.WF
            apply Assoc.WellFormed.val <;> assumption
        · rfl
    · case all.refl k S₁ S₂ U₁ U₂ L S₁.Shape S₂.Shape S.Sub U.Sub S.IH U.IH =>
      apply all (L ∪ Env.dom Γ ∪ Env.dom Δ)
      · exact S.IH Θ.WF rfl
      · apply Shape_substituteVar
        · exact Var.WellFormed.toWellScoped u.WF
        · exact S₁.Shape
      · apply Shape_substituteVar
        · exact Var.WellFormed.toWellScoped u.WF
        · exact S₂.Shape
      · intros X X.Fresh
        rw [
          <- Typ.substituteVar_fresh (T := .var (.free X)) (x := z) (u := u) (by clear * - X.Fresh; aesop),
          <- substituteVar_instantiateRecTyp,
          <- substituteVar_instantiateRecTyp
        ]
        conv in (_ ▷ _) =>
          rw [<- Env.concat_cons]
          rhs
          change Env.substituteVar (Δ ▷ X <: S₂) z u
          rfl
        apply U.IH X (by clear * - X.Fresh; aesop)
        · rw [Env.concat_cons]
          apply Env.WellFormed.cons Θ.WF
          · clear * - X.Fresh
            simp [Assoc.dom]
            aesop
          · have S₂.WF : Typ.WellFormed (Γ ▷ z ⦂ .cap S C ++ Δ) S₂ :=
              (regular S.Sub).2.1
            apply Assoc.WellFormed.sub <;> assumption
        · rfl
    · case box.refl T₁ T₂ T.Sub T.IH =>
      exact box (T.IH Θ.WF rfl)
end Typ.Sub
