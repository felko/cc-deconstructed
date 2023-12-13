import CCDeconstructed.CC
import CCDeconstructed.Var
import CCDeconstructed.Syntax
import CCDeconstructed.Classes
import CCDeconstructed.Infrastructure
import CCDeconstructed.WellFormedness
import CCDeconstructed.Subcapturing
import CCDeconstructed.Subtyping

set_option linter.unusedVariables false

open CC Feature VarCat

inductive Adapt : Env cc3 → Typ cc3 → Typ cc3 → Cap cc3 → Cap cc3 → Prop where
  | refl_tvar {Γ : Env cc3} {X : Atom (.tvar cc3)} {C : Cap cc3} :
      Env.WellFormed Γ →
      Cap.WellFormed Γ C →
      Adapt Γ X X C C
  | left_tvar {Γ : Env cc3} {X : Atom (.tvar cc3)} {S T : Typ cc3} {C C₁ C₂ : Cap cc3} :
      X <: .cap S C ∈ Γ ∨ X ≔ .cap S C ∈ Γ →
      Adapt Γ (.cap S C) T (C₁ ∪ C) C₂ →
      Adapt Γ X T C₁ C₂
  | right_tvar {Γ : Env cc3} {X : Atom (.tvar cc3)} {S T : Typ cc3} {C C₁ C₂ : Cap cc3} :
      X ≔ .cap S C ∈ Γ →
      Adapt Γ T (.cap S C) C₁ C₂ →
      Adapt Γ T X C₁ ∅
  | top {Γ : Env cc3} {S : Typ cc3} {C : Cap cc3} :
      Env.WellFormed Γ →
      Typ.WellFormed Γ S →
      Cap.WellFormed Γ C →
      Adapt Γ S .top C C
  | arr {Γ : Env cc3} {S₁ S₂ : Typ cc3} {D₁ D₂ : Cap cc3} {U₁ U₂ : Typ cc3} (L : Finset (Atom (.var cc3))) {C C₁ C₂ : Cap cc3} :
      Adapt Γ (.cap S₂ D₂) (.cap S₁ D₂) C₁ C →
      ∀ x ∉ L, Adapt (Γ ▷ x ⦂ .cap S₂ D₂) (U₁.instantiateRecVar 0 x) (U₂.instantiateRecVar 0 x) C C₂ →
      Adapt Γ (.arr (.cap S₁ D₁) U₁) (.arr (.cap S₂ D₂) U₂) C₁ C₂
  | all {Γ : Env cc3} {k : TypevarKind cc3} {S₁ S₂ : Typ cc3} {U₁ U₂ : Typ cc3} (L : Finset (Atom (.tvar cc3))) {C₁ C₂ : Cap cc3} :
      Typ.Sub Γ S₂ S₁ →
      ∀ X ∉ L, Adapt (Γ ▷ X <: S₂) (U₁.instantiateRecTyp 0 X) (U₂.instantiateRecTyp 0 X) C₁ C₂ →
      Adapt Γ (.all k S₁ U₁) (.all k S₂ U₂) C₁ C₂
  | cap {Γ : Env cc3} {S₁ S₂ : Typ cc3} {D₁ D₂ : Cap cc3} {C : Cap cc3} :
      Typ.Sub Γ S₁ S₂ →
      Cap.Sub Γ C₁ C₂ →
      Cap.WellFormed Γ C →
      Adapt Γ (.cap S₁ D₁) (.cap S₂ D₂) C C
