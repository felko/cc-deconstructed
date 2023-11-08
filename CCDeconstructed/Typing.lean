import CCDeconstructed.CC
import CCDeconstructed.Var
import CCDeconstructed.Syntax
import CCDeconstructed.WellFormedness

open Feature VarCat

variable {i : CC}

class Sub (α : Typ) where
  Rel : Env i -> α -> α -> Prop
  refl : Reflexive Rel
  trans : Transitive Rel
  regular : Rel Γ x y -> WellFormed Γ ∧ WellFormed x ∧ WellFormed y

section Subtyping
  set_option hygiene false
  notation:30 Γ " ⊢ " T " <: " U => Subtyping Γ T U

  inductive Subtyping : Env i -> Typ i -> Typ i -> Prop where
    | reflTvar (X : Atom (tvar i)) :
        Env.WellFormed Γ ->
        Atom.WellFormed Γ X ->

end Subtyping

notation:30 Γ " ⊢ " T " <: " U => Sub.Rel Γ T U

set_option hygiene false
notation:30 C "; " Γ " ⊢ " e " : " T => Typing C Γ e T

inductive Typing : Cap i -> Env i -> Exp i -> Typ i -> Prop :=
  | var (x : Atom (var i)) :
      x ⦂ T ∈ Γ ->
      {.free x}; Γ ⊢ x : T
  |
