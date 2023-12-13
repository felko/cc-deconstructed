import CCDeconstructed.CC
import CCDeconstructed.Var
import CCDeconstructed.Syntax
import CCDeconstructed.Classes
import CCDeconstructed.Infrastructure
import CCDeconstructed.WellFormedness
import CCDeconstructed.Subcapturing
import CCDeconstructed.Subtyping
import CCDeconstructed.Substitution

set_option linter.unusedVariables false

open CC Feature VarCat

inductive Typing : Cap cc0 → Env cc0 → Exp cc0 → Typ cc0 → Prop :=
  | var {Γ : Env cc0} {x : Atom (var cc0)} {S : Typ cc0} {C : Cap cc0} :
      Env.WellFormed Γ →
      x ⦂ .cap S C ∈ Γ →
      Typing {.free x} Γ x (.cap S {.free x})
  | abs {C : Cap cc0} {Γ : Env cc0} {S : Typ cc0} {D : Cap cc0} {e : Exp cc0} (L : Finset (Atom (.var cc0))) :
      Typ.WellFormed Γ (.cap S D) →
      (∀ x ∉ L, Typing C (Γ ▷ x ⦂ .cap S D) (e.instantiateRecVar 0 x) (U.instantiateRecVar 0 x)) →
      Typing C Γ (.abs (.cap S D) e) (.cap (.arr (.cap S D) U) C)
  | app {C₁ C₂ : Cap cc0} {Γ : Env cc0} {f x : Atom (.var cc0)} {S : Typ cc0} {D : Cap cc0} {U : Typ cc0} {C : Cap cc0} :
     Typing C₁ Γ (.var f) (.cap (.arr (.cap S D) U) C) →
     Typing C₂ Γ (.var x) (.cap S C) →
     Typing (C₁ ∪ C₂) Γ (.app f x) (U.instantiateRecVar 0 (.free x))
  | tabs {Γ : Env cc0} {k : TypevarKind cc0} {S : Typ cc0} {e : Exp cc0} {U : Typ cc0} {C : Cap cc0} (L : Finset (Atom (.tvar cc0))) :
      Typ.WellFormed Γ S →
      Typ.Shape S →
      (∀ X ∉ L, Typing C (Γ ▷ X <: S) (e.instantiateRecTyp 0 X) (U.instantiateRecTyp 0 X)) →
      Typing C Γ (.tabs k S e) (.cap (.all k S U) C)
  | tapp {C₁ : Cap cc0} {Γ : Env cc0} {x : Atom (.var cc0)} {R : Typ cc0} {k : TypevarKind cc0} {S U : Typ cc0} {C : Cap cc0} :
      Typ.WellFormed Γ R →
      Typing C₁ Γ (.var x) (.cap (.all k S U) C) →
      Typ.Sub Γ R S →
      Typing C₁ Γ (.tapp x R) (U.instantiateRecTyp 0 R)
  | box {C₁ : Cap cc0} {Γ : Env cc0} {x : Atom (.var cc0)} {S : Typ cc0} {C : Cap cc0} :
      Typing C₁ Γ x (.cap S C) →
      Typing ∅ Γ (.box x) (.cap (.box (.cap S C)) ∅)
  | unbox {Γ : Env cc0} {x : Atom (.var cc0)} {S : Typ cc0} {C : Cap cc0} :
      Typing ∅ Γ x (.box (.cap S C)) →
      Typing C Γ (.unbox x) (.cap S C)
  | let_ {C₁ C₂ : Cap cc0} {Γ : Env cc0} {e₁ e₂ : Exp cc0} {T U : Typ cc0} (L : Finset (Atom (.var cc0))):
      Typing C₁ Γ e₁ T →
      (∀ x ∉ L, Typing C₂ (Γ ▷ x ⦂ T) (e₂.instantiateRecVar 0 x) U) →
      Typing (C₁ ∪ C₂) Γ (.let_ e₁ e₂) U
  | sub {C : Cap cc0} {Γ : Env cc0} {e : Exp cc0} (T : Typ cc0) {U : Typ cc0} :
      Typing C Γ e T →
      Typ.Sub Γ T U →
      Typ.WellFormed Γ U →
      Typing C Γ e U

namespace Typing
  namespace Inversion
    @[aesop unsafe]
    lemma var {C : Cap cc0} {Γ : Env cc0} {x : Atom (.var cc0)} {T : Typ cc0} :
      Typing C Γ x T →
      ∃ S₁ S₂ D₁ D₂, x ⦂ .cap S₁ D₁ ∈ Γ
           ∧ T = .cap S₂ D₂
           ∧ Typ.Sub Γ S₁ S₂
           ∧ Cap.Sub Γ {.free x} D₂
    := by
      intros Ty
      generalize Eq.gen : Exp.var (.free x) = e at Ty
      induction Ty <;> cases Eq.gen
      · case var.refl Γ S C Γ.WF x.Mem =>
        exists S, S, C, {.free x}
        have xSC.WF : Assoc.WellFormed Γ (x ⦂ .cap S C) :=
          Env.WellFormed.mem Γ.WF x.Mem
        cases xSC.WF
        case val S.WF S.Shape C.WF =>
        apply And.intro x.Mem (And.intro rfl (And.intro _ _))
        · apply Typ.Sub.reflexivity Γ.WF S.WF
        · apply Cap.Sub.reflexivity Γ.WF
          simp [Cap.WellFormed,Var.WellFormed]
          apply Env.dom_mem_iff.mpr
          exists .val, .cap S C
      · case sub.refl C Γ T U Sub U.WF Ty IH =>
        obtain ⟨S₁, ⟨S₂, ⟨D₁, ⟨D₂, ⟨x.Mem, ⟨T.Eq, ⟨S.Sub₁₂, D.Sub₁₂⟩⟩⟩⟩⟩⟩⟩ := IH rfl
        clear IH
        cases T.Eq
        obtain ⟨S₃, ⟨D₃, ⟨U.Eq, ⟨S.Sub₂₃, D.Sub₂₃⟩⟩⟩⟩ := Typ.Sub.Inversion.cap Sub
        cases U.Eq
        exists S₁, S₃, D₁, D₃
        apply And.intro x.Mem (And.intro rfl (And.intro _ _))
        · exact Typ.Sub.transitivity S₂ S.Sub₁₂ S.Sub₂₃
        · exact Cap.Sub.transitivity D₂ D.Sub₁₂ D.Sub₂₃
  end Inversion

  @[aesop unsafe]
  def regular {C : Cap cc0} {Γ : Env cc0} {e : Exp cc0} {T : Typ cc0} :
    Typing C Γ e T →
      Cap.WellFormed Γ C
    ∧ Env.WellFormed Γ
    ∧ Exp.WellScoped e
    ∧ Typ.WellFormed Γ T
  := by
    intros Ty
    induction Ty
    · case var Γ x S C Γ.WF x.Mem =>
      have xSC.WF : Assoc.WellFormed Γ (x ⦂ .cap S C) :=
        Env.WellFormed.mem Γ.WF x.Mem
      obtain ⟨S.WF, S.Shape, C.WF⟩ := xSC.WF
      have x.In : x ∈ Env.dom Γ :=
        Env.dom_mem_iff.mpr ⟨.val, ⟨.cap S C, x.Mem⟩⟩
      have x.WF : Cap.WellFormed Γ {.free x} :=
        Cap.WellFormed.singleton x.In
      have x.WS : Exp.WellScoped (.var (.free x)) := by
        apply Exp.WellScoped.var
        simp [Var.WellScoped]
      have Sx.WF : Typ.WellFormed Γ (.cap S {.free x}) :=
        Typ.WellFormed.cap S.WF S.Shape x.WF
      exact ⟨x.WF, ⟨Γ.WF, ⟨x.WS, Sx.WF⟩⟩⟩
    · case abs U C Γ S D e L SD.WF e.Ty IH =>
      pick_fresh x ∉ L ∪ Cap.fv C
      obtain ⟨C.WF, ⟨ΓSD.WF, ⟨e.WS, U.WF⟩⟩⟩ := IH x (by clear * - x.Fresh; aesop)
      cases ΓSD.WF; rename_i Γ.WF x.NotIn xSD.WF
      cases xSD.WF; rename_i S.WF S.Shape D.WF
      apply And.intro _ (And.intro Γ.WF (And.intro _ _))
      · intros v v.In
        pick_fresh x ∉ L ∪ Cap.fv C
        obtain ⟨C.WF, ⟨ΓSD.WF, ⟨e.WS, U.WF⟩⟩⟩ := IH x (by clear * - x.Fresh; aesop)
        specialize C.WF v v.In
        cases v <;> simp [Var.WellFormed] at *
        case free y =>
        cases C.WF
        · case inl y.In =>
          exact y.In
        · case inr y.Eq =>
          simp [Assoc.dom] at y.Eq
          cases y.Eq
          replace v.In := Cap.mem_free_iff_mem_fv.mp v.In
          exfalso
          apply x.Fresh (Or.inr v.In)
      · apply Exp.WellScoped.abs L
        · exact Typ.WellFormed.toWellScoped (Typ.WellFormed.cap S.WF S.Shape D.WF)
        · intros x x.Fresh
          obtain ⟨C.WF, ⟨ΓSD.WF, ⟨e.WS, U.WF⟩⟩⟩ := IH x (by clear * - x.Fresh; aesop)
          exact e.WS
      · apply Typ.WellFormed.cap
        · apply Typ.WellFormed.arr L S.WF S.Shape D.WF
          intros x x.Fresh
          obtain ⟨C.WF, ⟨ΓSD.WF, ⟨e.WS, U.WF⟩⟩⟩ := IH x (by clear * - x.Fresh; aesop)
          exact U.WF
        · apply Typ.Shape.arr L S.Shape (Cap.WellFormed.toWellScoped D.WF)
          intros x x.Fresh
          obtain ⟨C.WF, ⟨ΓSD.WF, ⟨e.WS, U.WF⟩⟩⟩ := IH x (by clear * - x.Fresh; aesop)
          exact Typ.WellFormed.toWellScoped U.WF
        · intros v v.In
          have v.WF := C.WF v v.In
          clear * - v.WF v.In x.Fresh
          cases v <;> simp [Var.WellFormed,Assoc.dom] at *
          case a.free y =>
          cases v.WF
          · case inl v.In =>
            exact v.In
          · case inr v.Eq =>
            cases v.Eq
            exfalso
            exact x.Fresh (Or.inr (Cap.mem_free_implies_mem_fv v.In))
    · case app C₁ C₂ Γ f x S D U C f.Ty x.Ty f.IH x.IH =>
      obtain ⟨C₁.WF, ⟨Γ.WF, ⟨⟨f.WS⟩, SDUC.WF⟩⟩⟩ := f.IH
      obtain ⟨C₂.WF, ⟨Γ.WF, ⟨⟨x.WS⟩, SC.WF⟩⟩⟩ := x.IH
      cases SDUC.WF; rename_i SDU.Shape SDU.WF C.WF
      cases SDU.WF; rename_i L S.Shape S.WF D.WF U.WF
      apply And.intro _ (And.intro Γ.WF (And.intro _ _))
      · exact Cap.WellFormed.union C₁.WF C₂.WF
      · exact Exp.WellScoped.app f.WS x.WS
      · pick_fresh y ∉ L ∪ Env.dom Γ ∪ Typ.fvVar U
        specialize U.WF y (by clear * - y.Fresh; aesop)
        rw [Typ.substituteVar_instantiateRecVar_intro (x := y) (by clear * - y.Fresh; aesop)]
        rw [<- Env.concat_nil (Γ := Γ)]
        conv in ∅ =>
          change Env.substituteVar ∅ y x
          rfl
        apply Typ.WellFormed.substitutionVal (U := .cap S D) (allowCap := false)
        · simp
          apply Env.WellFormed.cons Γ.WF
          · simp
            clear * - y.Fresh
            aesop
          · exact Assoc.WellFormed.val S.WF S.Shape D.WF
        · obtain ⟨S₁, ⟨S₂, ⟨D₁, ⟨D₂, ⟨x.Mem, ⟨⟨S.Eq, C.Eq⟩, ⟨S.Sub, D.Sub⟩⟩⟩⟩⟩⟩⟩ := Inversion.var x.Ty
          simp [Var.WellFormed]
          apply Env.dom_mem_iff.mpr
          exists .val, .cap S₁ D₁
        · exact U.WF
    · case tabs Γ k S e U C L S.WF S.Shape e.Ty IH =>
      pick_fresh X ∉ L
      obtain ⟨C.WF, ⟨ΓS.WF, ⟨e.WS, U.WF⟩⟩⟩ := IH X (by clear * - X.Fresh; aesop)
      cases ΓS.WF; rename_i Γ.WF x.NotIn XS.WF
      cases XS.WF; rename_i S.WF S.Shape
      apply And.intro _ (And.intro Γ.WF (And.intro _ _))
      · intros v v.In
        have v.WF := C.WF v v.In
        clear * - v.WF
        cases v <;> simp [Var.WellFormed,Assoc.dom] at *
        exact v.WF
      · apply Exp.WellScoped.tabs L
        · exact Typ.WellFormed.toWellScoped S.WF
        · intros X X.Fresh
          obtain ⟨C.WF, ⟨ΓSD.WF, ⟨e.WS, U.WF⟩⟩⟩ := IH X (by clear * - X.Fresh; aesop)
          exact e.WS
      · apply Typ.WellFormed.cap
        · apply Typ.WellFormed.all L S.WF S.Shape
          intros X X.Fresh
          obtain ⟨C.WF, ⟨ΓSD.WF, ⟨e.WS, U.WF⟩⟩⟩ := IH X (by clear * - X.Fresh; aesop)
          exact U.WF
        · apply Typ.Shape.all L S.Shape
          intros X X.Fresh
          obtain ⟨C.WF, ⟨ΓSD.WF, ⟨e.WS, U.WF⟩⟩⟩ := IH X (by clear * - X.Fresh; aesop)
          apply Typ.WellFormed.toWellScoped U.WF
        · intros v v.In
          have v.WF := C.WF v v.In
          clear * - v.WF
          cases v <;> simp [Var.WellFormed,Assoc.dom] at *
          exact v.WF
    · case tapp C₁ Γ x R k S U C R.WF x.Ty Sub x.IH =>
      obtain ⟨C₁.WF, ⟨Γ.WF, ⟨⟨x.WS⟩, kSUC.WF⟩⟩⟩ := x.IH
      cases kSUC.WF; rename_i kSU.Shape kSU.WF C.WF
      cases kSU.WF; rename_i L S.Shape S.WF U.WF
      apply And.intro C₁.WF (And.intro Γ.WF (And.intro _ _))
      · exact Exp.WellScoped.tapp x.WS (Typ.WellFormed.toWellScoped R.WF)
      · pick_fresh X ∉ L ∪ Env.dom Γ ∪ Typ.fvTyp U
        specialize U.WF X (by clear * - X.Fresh; aesop)
        rw [Typ.substituteTyp_instantiateRecTyp_intro (X := X) (by clear * - X.Fresh; aesop)]
        rw [<- Env.concat_nil (Γ := Γ)]
        conv in ∅ =>
          change Env.substituteTyp ∅ X R
          rfl
        apply Typ.WellFormed.substitutionSub (U := R)
        · simp
          apply Env.WellFormed.cons Γ.WF
          · simp
            clear * - X.Fresh
            aesop
          · apply Assoc.WellFormed.sub R.WF
            exact (Typ.Sub.Shape_iff Sub).mpr S.Shape
        · apply Typ.WellFormed.ignore_bindings (T := S)
          simp
          exact U.WF
    · case box C₁ Γ x S C x.Ty x.IH =>
      obtain ⟨C₁.WF, ⟨Γ.WF, ⟨⟨x.WS⟩, SC.WF⟩⟩⟩ := x.IH
      have SC.WF' := SC.WF
      cases SC.WF'; rename_i S.Shape S.WF C.WF
      apply And.intro Cap.WellFormed.empty (And.intro Γ.WF (And.intro _ _))
      · exact Exp.WellScoped.box x.WS
      · apply Typ.WellFormed.cap
        · exact Typ.WellFormed.box SC.WF
        · exact Typ.Shape.box (Typ.WellFormed.toWellScoped SC.WF)
        · exact Cap.WellFormed.empty
    · case unbox Γ x S C x.Ty x.IH =>
      obtain ⟨C₁.WF, ⟨Γ.WF, ⟨⟨x.WS⟩, bSC.WF⟩⟩⟩ := x.IH
      cases bSC.WF; rename_i SC.WF
      have SC.WF' := SC.WF
      cases SC.WF'; rename_i S.WF S.Shape C.WF
      apply And.intro C.WF (And.intro Γ.WF (And.intro _ _))
      · exact Exp.WellScoped.unbox x.WS
      · exact SC.WF
    · case let_ C₁ C₂ Γ e₁ e₂ T U L e₁.Ty e₂.Ty e₁.IH e₂.IH =>
      pick_fresh x ∉ L ∪ Cap.fv C₂ ∪ Typ.fvVar U
      obtain ⟨C₁.WF, ⟨Γ.WF, ⟨e₁.WS, T.WF⟩⟩⟩ := e₁.IH
      obtain ⟨C₂.WF, ⟨ΓxT.WF, ⟨e₂.WS, U.WF⟩⟩⟩ := e₂.IH x (by clear * - x.Fresh; aesop)
      apply And.intro _ (And.intro _ (And.intro _ _))
      · apply Cap.WellFormed.union C₁.WF
        intros v v.In
        have v.WF := C₂.WF v v.In
        clear * - x.Fresh v.WF v.In
        cases v <;> simp [Var.WellFormed] at *
        case free y =>
        cases v.WF
        · case inl v.In =>
          exact v.In
        · case inr v.Eq =>
          simp [Assoc.dom] at v.Eq
          cases v.Eq
          exfalso
          exact x.Fresh (Or.inr (Or.inl (Cap.mem_free_implies_mem_fv v.In)))
      · exact Γ.WF
      · apply Exp.WellScoped.let_ L e₁.WS
        intros y y.Fresh
        obtain ⟨C₂.WF, ⟨ΓxT.WF, ⟨e₂.WS, U.WF⟩⟩⟩ := e₂.IH y (by clear * - y.Fresh; aesop)
        exact e₂.WS
      · rw [<- Env.concat_nil (Γ := Γ ▷ x ⦂ T)] at U.WF
        conv in Γ =>
          rw [<- Env.concat_nil (Γ := Γ)]
          rhs
          change Env.substituteCap ∅ x ∅
          rfl
        rw [<- Typ.substituteCap_fresh (T := U) (x := x) (D := ∅) (by clear * - x.Fresh; aesop)]
        apply Typ.WellFormed.substitutionCap (U := T)
        · simp
          exact ΓxT.WF
        · exact Cap.WellFormed.empty
        · exact U.WF
    · case sub C Γ e T U e.Ty Sub U.WF e.IH =>
      obtain ⟨C.WF, ⟨Γ.WF, ⟨e.WS, T.WF⟩⟩⟩ := e.IH
      exact And.intro C.WF (And.intro Γ.WF (And.intro e.WS U.WF))

  @[aesop unsafe]
  lemma weaken {C : Cap cc0} {Γ Θ Δ : Env cc0} {e : Exp cc0} {T : Typ cc0} :
    Env.WellFormed (Γ ++ Θ ++ Δ) →
    Typing C (Γ ++ Δ) e T →
    Typing C (Γ ++ Θ ++ Δ) e T
  := by
    intros ΓΘΔ.WF e.Ty
    generalize Eq.gen : Γ ++ Δ = ΓΔ at e.Ty
    induction e.Ty generalizing Δ <;> cases Eq.gen
    · case var.refl x S C ΓΔ.WF x.Mem =>
      apply var ΓΘΔ.WF (C := C)
      simp at *
      cases x.Mem
      · case inl x.Mem =>
        exact Or.inl (Or.inl x.Mem)
      · case inr x.Mem =>
        exact Or.inr x.Mem
    · case abs.refl U C S D e L SD.WF e.Ty e.IH =>
      apply abs (L ∪ Env.dom Γ ∪ Env.dom Θ ∪ Env.dom Δ)
      · exact Typ.WellFormed.weaken SD.WF (Env.WellFormed.Nodup ΓΘΔ.WF)
      · intros x x.Fresh
        rw [<- Env.concat_cons]
        apply e.IH x (by clear * - x.Fresh; aesop)
        · rw [Env.concat_cons]
          apply Env.WellFormed.cons ΓΘΔ.WF (by clear * - x.Fresh; aesop)
          apply Assoc.WellFormed.weaken _ (Env.WellFormed.Nodup ΓΘΔ.WF)
          cases SD.WF; rename_i S.Shape S.WF D.WF
          exact Assoc.WellFormed.val S.WF S.Shape D.WF
        · rfl
    · case app.refl C₁ C₂ f x S D U C f.Ty x.Ty f.IH x.IH =>
      apply app
      · exact f.IH ΓΘΔ.WF rfl
      · exact x.IH ΓΘΔ.WF rfl
    · case tabs.refl k S e U C L S.Shape S.WF e.Ty e.IH =>
      apply tabs (L ∪ Env.dom Γ ∪ Env.dom Θ ∪ Env.dom Δ)
      · exact Typ.WellFormed.weaken S.WF (Env.WellFormed.Nodup ΓΘΔ.WF)
      · exact S.Shape
      · intros X X.Fresh
        rw [<- Env.concat_cons]
        apply e.IH X (by clear * - X.Fresh; aesop)
        · rw [Env.concat_cons]
          apply Env.WellFormed.cons ΓΘΔ.WF (by clear * - X.Fresh; aesop)
          apply Assoc.WellFormed.weaken _ (Env.WellFormed.Nodup ΓΘΔ.WF)
          exact Assoc.WellFormed.sub S.WF S.Shape
        · rfl
    · case tapp.refl C₁ x R k S U C R.WF x.Ty R.Sub x.IH =>
      apply tapp
      · exact Typ.WellFormed.weaken R.WF (Env.WellFormed.Nodup ΓΘΔ.WF)
      · exact x.IH ΓΘΔ.WF rfl
      · exact Typ.Sub.weaken R.Sub ΓΘΔ.WF
    · case box.refl C₁ x S C x.Ty x.IH =>
      exact box (x.IH ΓΘΔ.WF rfl)
    · case unbox.refl x S C x.Ty x.IH =>
      exact unbox (x.IH ΓΘΔ.WF rfl)
    · case let_ C₁ C₂ e₁ e₂ T U L e₁.Ty e₂.Ty e₁.IH e₂.IH =>
      apply let_ (L ∪ Env.dom Γ ∪ Env.dom Θ ∪ Env.dom Δ)
      · exact e₁.IH ΓΘΔ.WF rfl
      · intros x x.Fresh
        rw [<- Env.concat_cons]
        apply e₂.IH x (by clear * - x.Fresh; aesop)
        · rw [Env.concat_cons]
          apply Env.WellFormed.cons ΓΘΔ.WF (by clear * - x.Fresh; aesop)
          apply Assoc.WellFormed.weaken _ (Env.WellFormed.Nodup ΓΘΔ.WF)
          obtain ⟨_, ⟨ΓxT, _⟩⟩ := regular (e₂.Ty x (by clear * - x.Fresh; aesop))
          cases ΓxT; rename_i ΓΔ.WF x.NotIn xT.WF
          exact xT.WF
        · rw [Env.concat_cons]
    · case sub C e T U e.Ty Sub U.WF e.IH =>
      apply sub (T := T)
      · exact e.IH ΓΘΔ.WF rfl
      · exact Typ.Sub.weaken Sub ΓΘΔ.WF
      · exact Typ.WellFormed.weaken U.WF (Env.WellFormed.Nodup ΓΘΔ.WF)

  @[aesop unsafe]
  lemma substitutionVar {Γ Δ : Env cc0} {z : Atom (.var cc0)} {u : Atom (.var cc0)} {S : Typ cc0} {C : Cap cc0} {e : Exp cc0} {T : Typ cc0} :
    Typing C Γ u (.cap S D) →
    Typing C (Γ ▷ z ⦂ .cap S D ++ Δ) e T →
    Typing (C.substituteVar z u) (Γ ++ Δ.substituteVar z u) (e.substituteVar z u) (T.substituteVar z u)
  := by
    intros u.Ty e.Ty
    obtain ⟨S₁, ⟨S₂, ⟨D₁, ⟨D₂, ⟨u.Mem, ⟨SD.Eq, ⟨S.Sub, D.Sub⟩⟩⟩⟩⟩⟩⟩ := Inversion.var u.Ty
    cases SD.Eq
    generalize Renaming.S : S = S₂ at *; clear S Renaming.S
    generalize Renaming.D : D = D₂ at *; clear D Renaming.D
    generalize Eq.gen : Γ ▷ z ⦂ .cap S₂ D₂ ++ Δ = Θ at e.Ty
    induction e.Ty <;> cases Eq.gen
    · case var.refl x S₃ D₃ Θ.WF x.Mem =>
      simp [Cap.substituteVar,Cap.substituteCap,Exp.substituteVar,Exp.substituteCap]
      split
      · case inl Eq =>
        cases Eq
        simp at x.Mem
        simp
        rcases x.Mem with ⟨⟨x.Mem⟩ | ⟨⟨⟩, ⟨⟩⟩⟩ | ⟨x.Mem⟩
        · apply var
          · apply Env.WellFormed.substitutionVal (allowCap := false) _ Θ.WF
            simp [Var.WellFormed]
            apply Env.dom_mem_iff.mpr
            exists .val, .cap S₁ D₁
          · sorry
end Typing
