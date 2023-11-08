import CCDeconstructed.Var
import CCDeconstructed.Syntax
import CCDeconstructed.CC
import CCDeconstructed.Env

open Feature VarCat

variable {i : CC}

namespace Var
  inductive WellFormed (Γ : Env i) : @Var i α -> Prop where
    | freeVar : x ∈ Γ.dom (var i) -> WellFormed Γ (@Var.free i (var i) x)
    | freeTVar : x ∈ Γ.dom (tvar i) -> WellFormed Γ (@Var.free i (tvar i) x)
    | cap : WellFormed Γ .cap
end Var

namespace Cap
  def WellFormed (Γ : Env i) (C : Cap i) : Prop :=
    ∀ v ∈ C, Var.WellFormed Γ v
end Cap

mutual
  inductive Typ.Type : Typ i -> Prop where
    | shape : Shape S -> Typ.Type S
    | cap : Shape S -> Cap.WellScoped C -> Typ.Type (.cap S C)

  inductive Typ.Shape : Typ i -> Prop where
    | var : Shape (.var (.free X))
    | top : Shape top
    | arr (L : Finset (Atom (.var i))) :
        Typ.Type T ->
        (∀ x ∉ L, Typ.Type (@Scoped.instantiate _ _ (.var i) _ U (.free x))) ->
        Typ.Shape (.arr T U)
    | all (L : Finset (Atom (.tvar i))) :
        Typ.Shape S ->
        (∀ X ∉ L, Typ.Type (@Scoped.instantiate _ _ (.tvar i) _ U (.var (.free X)))) ->
        Typ.Shape (.all k T U)
    | box [HasFeature i box_type] :
        Typ.Type T ->
        Typ.Shape (.box T)
end

inductive Typ.WellFormed : Env i -> Typ i -> Prop where
  | var : X <: R ∈ Γ -> Typ.WellFormed Γ X
  | top : Typ.WellFormed Γ .top
  | arr (L : Finset (Atom (.var i))) :
      Typ.WellFormed Γ T ->
      (∀ x ∉ L, Typ.WellFormed (Γ ▷ x ⦂ T) (@Scoped.instantiate _ _ (.var i) _ U (.free x))) ->
      Typ.WellFormed Γ (.arr T U)
  | all (L : Finset (Atom (.tvar i))) :
      Typ.WellFormed Γ S ->
      Typ.Shape S ->
      (∀ X ∉ L, Typ.WellFormed (Γ ▷ X <: S) (@Scoped.instantiate _ _ (.tvar i) _ U (.var (.free X)))) ->
      Typ.WellFormed Γ (.all k S U)
  | box :
      Typ.WellFormed Γ T ->
      Typ.WellFormed Γ (.box T)
  | cap :
      Typ.WellFormed Γ S ->
      Typ.Shape S ->
      Cap.WellFormed Γ C ->
      Typ.WellFormed Γ (.cap S C)

inductive Env.WellFormed : Env i -> Prop where
  | nil : Env.WellFormed ∅
  | val :
      Env.WellFormed Γ ->
      Typ.WellFormed Γ T ->
      Env.WellFormed (Γ ▷ x ⦂ T)
  | sub (S : Typ i) :
      Env.WellFormed Γ ->
      Typ.WellFormed Γ S ->
      Env.WellFormed (Γ ▷ x <: S)
  | typ [HasFeature i type_bindings] :
      Env.WellFormed Γ ->
      Typ.WellFormed Γ T ->
      Env.WellFormed (Γ ▷ X ≔ T)

lemma Var.WellFormed_WellScoped :
  Var.WellFormed Γ v ->
  Var.WellScoped v
:= by intros v.WF; cases v.WF <;> constructor

lemma Cap.WellFormed_WellScoped :
  Cap.WellFormed Γ C ->
  Cap.WellScoped C
:= by
  intros C.WF v v.In
  eapply Var.WellFormed_WellScoped
  apply C.WF; apply v.In

lemma Typ.WellFormed_Type :
  Env.WellFormed Γ ->
  Typ.WellFormed Γ T ->
  Typ.Type T
:= by
  intros Γ.WF T.WF
  induction T.WF
  · case var =>
    apply Typ.Type.shape Typ.Shape.var
  · case top =>
    apply Typ.Type.shape Typ.Shape.top
  · case arr Γ T U L T.WF U.WF T.IH U.IH =>
    apply Typ.Type.shape; apply Typ.Shape.arr
    · apply T.IH Γ.WF
    · intros x x.NotIn
      apply U.IH
      · apply x.NotIn
      · apply Env.WellFormed.val <;> assumption
  · case all Γ S U k L S.WF S.Shape U.WF S.IH U.IH =>
    apply Typ.Type.shape; apply Typ.Shape.all
    · apply S.Shape
    · intros x x.NotIn
      apply U.IH
      · apply x.NotIn
      · apply Env.WellFormed.sub <;> assumption
  · case box Γ T T.WF T.IH =>
    apply Typ.Type.shape; apply Typ.Shape.box
    apply T.IH Γ.WF
  · case cap Γ S C S.WF S.Shape C.WF S.IH =>
    apply Typ.Type.cap
    · apply S.Shape
    · eapply Cap.WellFormed_WellScoped C.WF
