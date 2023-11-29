import CCDeconstructed.CC
import CCDeconstructed.Var
import CCDeconstructed.Syntax
import CCDeconstructed.Classes
import CCDeconstructed.Infrastructure
import CCDeconstructed.WellFormedness

open Feature VarCat

variable {i : CC}

inductive Cap.Sub (Γ : Env i) : Cap i → Cap i → Prop where
  | elem :
    Env.WellFormed Γ →
    Cap.WellFormed Γ C →
    Var.WellFormed (allowCap := true) Γ v →
    v ∈ C →
    Cap.Sub Γ {v} C
  | set :
    Env.WellFormed Γ →
    Cap.WellFormed Γ D →
    (∀ v ∈ C, Cap.Sub Γ {v} D) →
    Cap.Sub Γ C D
  | var :
    Env.WellFormed Γ →
    x ⦂ .cap S C ∈ Γ →
    Cap.Sub Γ {.free x} C

namespace Cap.Sub
  lemma regular :
    Sub Γ C D →
    Env.WellFormed Γ ∧ WellFormed Γ C ∧ WellFormed Γ D
  := by
    intros Sub
    induction Sub
    · case elem C v Γ.WF C.WF v.WF v.In =>
      apply And.intro Γ.WF
      apply And.intro _ C.WF
      intros w w.In
      simp at w.In; cases w.In
      exact v.WF
    · case set D C Γ.WF D.WF Elem.Sub IH =>
      apply And.intro Γ.WF (And.intro _ D.WF)
      cases (Finset.eq_empty_or_nonempty C)
      · case inl C.Empty =>
        rw [C.Empty]
        exact Cap.WellFormed_empty
      · case inr C.Nonempty =>
        obtain ⟨v, v.In⟩ := C.Nonempty

  lemma empty :
    Env.WellFormed Γ →
    WellFormed Γ C →
    Sub Γ ∅ C
  := by
    intros Γ.WF C.WF
    apply Sub.set Γ.WF C.WF
    simp

  lemma WellFormed_in_empty_env_is_at_most_cap :
    WellFormed ∅ C →
    C ⊆ {@Var.cap i _ rfl}
  := by
    intros WF
    intros v v.In
    simp
    simp [WellFormed] at WF
    specialize WF v v.In
    cases v <;> simp only [Var.WellFormed] at WF
    · case free x =>
      have : Env.dom (α := .var i) ∅ = ∅ := by
        apply Env.dom_empty
      simp [this] at WF
    · case cap => rfl

  lemma cap :
    WellFormed (i := i) Γ C →
    Sub (i := i) Γ C {@Var.cap i _ rfl}
  := by
    intros C.WF
    induction Γ
    · case empty =>
      have C.AtMostCap := WellFormed_in_empty_env_is_at_most_cap C.WF
      simp at C.AtMostCap
      cases C.AtMostCap
      · case inl C.Empty =>
        rw [C.Empty]
        apply set
        intros v v.In
        simp at v.In
      · case inr C.IsCap =>
        rw [C.IsCap]
        apply elem
        simp
    · case val x T Γ x.NotIn IH =>
      have : ∀ y ∈ C, Sub Γ {y} {.cap} :=
        apply set
      apply set

      simp [WellFormed,Var.WellFormed,Env.dom,Finset.fold,List.foldr] at C.WF
      cases C.decidableNonempty
      · case isFalse h =>
        simp at h
        rw [h]
        apply empty
        intros v v.In
        simp at v.In
        rw [v.In]
        constructor
      · case isTrue h =>
        obtain ⟨v, v.In⟩ := h
        specialize C.WF v v.In
        cases v <;> simp at C.WF
        apply Sub.elem




  lemma reflexivity :
    Sub Γ C C
  := by
    apply Sub.set
    intros x x.In
    apply Sub.elem x.In

  lemma distributivity :
    Sub Γ C D →
    ∀ v ∈ C, Sub Γ {v} D
  := by
    intros CD
    cases CD
    · case elem v v.In =>
      intros w w.In
      have Eq : v = w := by aesop
      rw [<- Eq] at *
      apply Sub.elem v.In
    · case set Elem =>
      exact Elem
    · case var x S x.Bound =>
      intros v v.In
      cases v
      · case free y =>
        have Eq : x = y := by aesop
        rw [<- Eq] at *
        apply Sub.var x.Bound
      · case bound k =>
        exfalso; aesop
      · case cap =>
        exfalso; aesop

  lemma transitivity C₂ :
    Sub Γ C₁ C₂ →
    Sub Γ C₂ C₃ →
    Sub Γ C₁ C₃
  := by
    intros Sub₁₂ Sub₂₃
    induction Sub₁₂
    · case elem x C x.In =>
      apply distributivity Sub₂₃ x x.In
    · case set C₁ C₂ Elem IH =>
      apply Sub.set
      intros v v.In
      apply IH v v.In Sub₂₃
    · case var x S C₂ x.Bound =>
      apply Sub.var
end Cap.Sub
