import CCDeconstructed.CC
import CCDeconstructed.Var
import CCDeconstructed.Syntax
import CCDeconstructed.Classes
import CCDeconstructed.Infrastructure
import CCDeconstructed.WellFormedness

open Feature VarCat

set_option linter.unusedVariables false

variable {i : CC}

inductive Cap.Sub (Γ : Env i) : Cap i → Cap i → Prop where
  | elem {C : Cap i} {v : Var (.var i)} :
    Env.WellFormed Γ →
    Cap.WellFormed Γ C →
    v ∈ C →
    Cap.Sub Γ {v} C
  | set {C D : Cap i} :
    Env.WellFormed Γ →
    Cap.WellFormed Γ D →
    (∀ v ∈ C, Cap.Sub Γ {v} D) →
    Cap.Sub Γ C D
  | var {S : Typ i} {C D : Cap i} {x : Atom (.var i)} :
    x ⦂ .cap S C ∈ Γ →
    Cap.Sub Γ C D →
    Cap.Sub Γ {.free x} D

namespace Cap.Sub
  lemma regular {Γ : Env i} {C D : Cap i} :
    Sub Γ C D →
    Env.WellFormed Γ ∧ WellFormed Γ C ∧ WellFormed Γ D
  := by
    intros Sub
    induction Sub
    · case elem C v Γ.WF C.WF v.In =>
      apply And.intro Γ.WF
      apply And.intro _ C.WF
      intros w w.In
      simp at w.In; cases w.In
      exact C.WF v v.In
    · case set D C Γ.WF D.WF Elem.Sub IH =>
      apply And.intro Γ.WF (And.intro _ D.WF)
      intros v v.In
      obtain ⟨_, ⟨v.WF, _⟩⟩ := IH v v.In
      apply v.WF v (by simp)
    · case var S C D x x.In Sub IH =>
      obtain ⟨Γ.WF, C.WF, D.WF⟩ := IH
      apply And.intro Γ.WF (And.intro _ D.WF)
      intros y y.Eq
      simp at y.Eq
      cases y.Eq
      simp [Var.WellFormed]
      simp [Env.dom_mem_iff]
      exists .val, Typ.cap S C

  lemma empty {Γ : Env i} {C : Cap i} :
    Env.WellFormed Γ →
    WellFormed Γ C →
    Sub Γ ∅ C
  := by
    intros Γ.WF C.WF
    apply Sub.set Γ.WF C.WF
    simp

  lemma weaken {Γ Θ Δ : Env i} {C D : Cap i} :
    Cap.Sub (Γ ++ Δ) C D →
    Env.WellFormed (Γ ++ Θ ++ Δ) →
    Cap.Sub (Γ ++ Θ ++ Δ) C D
  := by
    intros Sub Γ.WF
    have Γ.Nodup : Env.Nodup (Γ ++ Θ ++ Δ) :=
      Env.WellFormed.Nodup Γ.WF
    induction Sub
    · case elem C v Γ'.WF C.WF v.In =>
      apply elem Γ.WF
      · exact Cap.WellFormed.weaken C.WF Γ.Nodup
      · exact v.In
    · case set D C Γ'.WF D.WF Elem.Sub IH =>
      apply set Γ.WF
      · exact Cap.WellFormed.weaken D.WF Γ.Nodup
      · exact IH
    · case var S C D x x.In Sub IH =>
      apply var (S := S) (by aesop) IH

  @[aesop unsafe]
  lemma weaken_head {Γ Δ : Env i} {C D : Cap i} :
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
  lemma weaken_cons {Γ : Env i} {C D : Cap i} {a : Assoc i} :
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

  @[aesop safe]
  lemma reflexivity {Γ : Env i} {C : Cap i} :
    Env.WellFormed Γ →
    WellFormed Γ C →
    Sub Γ C C
  := by
    intros Γ.WF C.WF
    apply Sub.set Γ.WF C.WF
    intros x x.In
    apply Sub.elem Γ.WF C.WF x.In

  @[aesop unsafe]
  lemma distributivity {Γ : Env i} {C D : Cap i} :
    Sub Γ C D →
    ∀ v ∈ C, Sub Γ {v} D
  := by
    intros CD
    cases CD
    · case elem v Γ.WF D.WF v.In =>
      intros w w.Eq
      simp at w.Eq
      cases w.Eq
      exact Sub.elem Γ.WF D.WF v.In
    · case set Elem =>
      exact Elem
    · case var S x Γ.WF D.WF x.In =>
      intros v v.In
      simp at v.In
      cases v.In
      exact Sub.var D.WF x.In

  @[aesop unsafe]
  lemma transitivity {Γ : Env i} {C₁ : Cap i} (C₂ : Cap i) {C₃ : Cap i} :
    Sub Γ C₁ C₂ →
    Sub Γ C₂ C₃ →
    Sub Γ C₁ C₃
  := by
    intros Sub₁₂ Sub₂₃
    induction Sub₁₂ generalizing C₃
    · case elem C₂ v Γ.WF C₂.WF v.In =>
      apply distributivity Sub₂₃ v v.In
    · case set C₁ C₂ Γ.WF C₂.WF Elem IH =>
      apply set Γ.WF ((regular Sub₂₃).2.2)
      intros v v.In
      apply IH v v.In Sub₂₃
    · case var S C₄ C₂ x x.In Sub₄₂ IH =>
      apply var x.In (IH Sub₂₃)

  lemma empty_env_is_at_most_cap {C : Cap i} :
    WellFormed ∅ C →
    C ⊆ {@Var.cap i _ rfl}
  := by
    intros WF
    intros v v.In
    simp
    simp [WellFormed] at WF
    specialize WF v v.In
    cases v <;> simp [Var.WellFormed] at WF
    rfl

  @[aesop safe]
  lemma cap {Γ : Env i} {C : Cap i} :
    Env.WellFormed Γ →
    WellFormed Γ C →
    Sub Γ C {@Var.cap i _ rfl}
  := by
    intros Γ.WF C.WF
    induction Γ.WF generalizing C
    · case nil =>
      have C.AtMostCap := empty_env_is_at_most_cap C.WF
      simp at C.AtMostCap
      cases C.AtMostCap
      · case inl C.Empty =>
        rw [C.Empty]
        exact set Env.WellFormed.nil Cap.WellFormed.cap (by simp)
      · case inr C.IsCap =>
        rw [C.IsCap]
        apply elem Env.WellFormed.nil Cap.WellFormed.cap (by simp)
    · case cons Γ a Γ.WF a.NotIn a.WF IH =>
      have Γ'.WF := Env.WellFormed.cons Γ.WF a.NotIn a.WF
      apply set
      · exact Γ'.WF
      · exact Cap.WellFormed.cap
      · intros v v.In
        have v.WF := C.WF v v.In
        cases a.WF
        · case a.val x S D S.WF S.Shape D.WF =>
          simp [Assoc.val] at a.NotIn
          simp [Var.WellFormed] at v.WF
          cases v <;> simp at *
          · case free y =>
            cases v.WF
            · case inl y.In =>
              apply weaken_cons
              · exact IH (Cap.WellFormed.singleton y.In)
              · exact Assoc.WellFormed.val S.WF S.Shape D.WF
              · exact a.NotIn
            · case inr y.Eq =>
              simp [Assoc.dom,Assoc.val] at y.Eq
              cases y.Eq
              apply var Env.mem_cons_head
              apply weaken_cons (IH D.WF) (by aesop) (by exact a.NotIn)
          · case cap =>
            apply elem Γ'.WF Cap.WellFormed.cap (by simp)
        · case a.sub X S S.WF S.Shape =>
          apply weaken_cons _ (by aesop) a.NotIn
          apply IH
          cases v <;> simp [Var.WellFormed,Assoc.dom,Assoc.val,Assoc.sub,Assoc.typ] at v.WF
          · case C.WF.free y =>
            apply Cap.WellFormed.singleton v.WF
          · case C.WF.cap =>
            exact Cap.WellFormed.cap
        · case a.typ X T T.WF =>
          apply weaken_cons _ (by aesop) a.NotIn
          apply IH
          cases v <;> simp [Var.WellFormed,Assoc.dom,Assoc.val,Assoc.sub,Assoc.typ] at v.WF
          · case C.WF.free y =>
            apply Cap.WellFormed.singleton v.WF
          · case C.WF.cap =>
            exact Cap.WellFormed.cap

  @[aesop safe]
  lemma mem_cap {Γ : Env i} {C : Cap i} :
    Env.WellFormed Γ →
    WellFormed Γ C →
    WellFormed Γ D →
    @Var.cap i _ rfl ∈ D →
    Sub Γ C D
  := by
    intros Γ.WF C.WF D.WF cap.Mem
    exact transitivity {.cap} (cap Γ.WF C.WF) (elem Γ.WF D.WF cap.Mem)

  lemma ignore_sub_bindings {Γ : Env i} {S₁ S₂ : Typ i} {Z : Atom (.tvar i)} {C₁ C₂ : Cap i} :
    Env.WellFormed (Γ ▷ Z <: S₁ ++ Δ) ->
    Cap.Sub (Γ ▷ Z <: S₂ ++ Δ) C₁ C₂ ->
    Cap.Sub (Γ ▷ Z <: S₁ ++ Δ) C₁ C₂
  := by
    intros ΓT₁Δ.WF C.Sub
    induction C.Sub
    · case elem C₂ v ΓT₂Δ.WF C₂.WF v.In =>
      apply Cap.Sub.elem ΓT₁Δ.WF
      · apply Cap.WellFormed.ignore_bindings
        apply C₂.WF
      · exact v.In
    · case set C₁ C₂ ΓT₂Δ.WF C₂.WF Sub IH =>
      apply Cap.Sub.set ΓT₁Δ.WF
      · apply Cap.WellFormed.ignore_bindings
        apply C₂.WF
      · exact IH
    · case var S₁ C₁ C₂ X X.Mem Sub IH =>
      apply Cap.Sub.var (S := S₁) (C := C₁) _ IH
      simp at X.Mem
      simp
      rcases X.Mem with ⟨X.Mem⟩ | ⟨X.Mem⟩
      · apply Or.inl X.Mem
      · apply Or.inr X.Mem
end Cap.Sub
