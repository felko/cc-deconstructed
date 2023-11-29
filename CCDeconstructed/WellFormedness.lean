import CCDeconstructed.Var
import CCDeconstructed.Syntax
import CCDeconstructed.CC
import CCDeconstructed.Infrastructure

open Feature VarCat Env

set_option linter.unusedVariables false

namespace Var
  def WellFormed {i : CC} {α : VarCat i} (allowCap := false) (Γ : Env i) : Var α → Prop
    | .free x => x ∈ dom Γ
    | .bound _ => False
    | .cap => if allowCap then True else False

  lemma WellFormed_WellScoped {α : VarCat i} (allowCap := false) {Γ : Env i} {v : Var α} :
    WellFormed allowCap Γ v →
    WellScoped allowCap v
  := by cases v <;> simp [WellFormed,WellScoped]

  @[aesop unsafe 40%]
  lemma WellFormed_weaken {α : VarCat i} (allowCap := false) {Γ Δ : Env i} {v : Var α} :
    WellFormed allowCap Δ v →
    WellFormed allowCap (Γ ++ Δ) v
  := by cases v <;> simp [WellFormed,Env.dom_concat]; aesop

  instance instWellFormedness {α : VarCat i} (allowCap : Bool) : WellFormedness i (Var α) where
    WellScoped := WellScoped allowCap
    WellScopedRec := WellScopedRec allowCap
    WellScoped_implies_WellScopedRec_0 := WellScoped_implies_WellScopedRec_0
    WellScopedRec_weaken := WellScopedRec_weaken
    WellFormed := WellFormed allowCap
    WellFormed_WellScoped := WellFormed_WellScoped allowCap
    WellFormed_weaken := WellFormed_weaken allowCap
end Var

namespace Cap
  def WellFormed (Γ : Env i) (C : Cap i) : Prop :=
    ∀ v ∈ C, Var.WellFormed (allowCap := true) Γ v

  lemma WellFormed_WellScoped :
    Cap.WellFormed Γ C →
    Cap.WellScoped C
  := by
    intros C.WF v v.In
    eapply Var.WellFormed_WellScoped
    apply C.WF; apply v.In

  @[simp]
  lemma WellFormed_empty :
    WellFormed Γ ∅
  := by simp [WellFormed]

  lemma WellFormed_union :
    WellFormed Γ C →
    WellFormed Γ D →
    WellFormed Γ (C ∪ D)
  := by
    simp [WellFormed]
    aesop

  @[aesop unsafe 40%]
  lemma WellFormed_weaken :
    WellFormed Δ C →
    WellFormed (Γ ++ Δ) C
  := fun WF v In => Var.WellFormed_weaken (allowCap := true) (WF v In)

  instance instWellFormedness : WellFormedness i (Cap i) where
    WellFormed := WellFormed
    WellFormed_WellScoped := WellFormed_WellScoped
    WellFormed_weaken := WellFormed_weaken
end Cap

mutual
  inductive Typ.Type : Typ i → Prop where
    | shape : Shape S → Typ.Type S
    | cap : Shape S → Cap.WellScoped C → Typ.Type (.cap S C)

  inductive Typ.Shape : Typ i → Prop where
    | var : Shape (.var (.free X))
    | top : Shape top
    | arr (L : Finset (Atom (.var i))) :
        Typ.Type T →
        (∀ x ∉ L, Typ.Type (Typ.instantiateRecVar U 0 (.free x))) →
        Typ.Shape (.arr T U)
    | all (L : Finset (Atom (.tvar i))) :
        Typ.Shape S →
        (∀ X ∉ L, Typ.Type (Typ.instantiateRecTyp U 0 (.var (.free X)))) →
        Typ.Shape (.all k T U)
    | box [HasFeature i box_type] :
        Typ.Type T →
        Typ.Shape (@Typ.box i _ T)
end

namespace Typ
  inductive WellFormed : Env i → Typ i → Prop where
    | var :
        X <: S ∈ Γ →
        WellFormed Γ X
    | top : WellFormed Γ .top
    | arr (L : Finset (Atom (.var i))) :
        WellFormed Γ T →
        (∀ x ∉ L, WellFormed (Γ ▷ x ⦂ T) (Typ.instantiateRecVar U 0 (.free x))) →
        WellFormed Γ (.arr T U)
    | all (L : Finset (Atom (.tvar i))) :
        WellFormed Γ S →
        Shape S →
        (∀ X ∉ L, Typ.WellFormed (Γ ▷ X <: S) (Typ.instantiateRecTyp U 0 (.var (.free X)))) →
        WellFormed Γ (.all k S U)
    | box [HasFeature i box_type] :
        WellFormed Γ T →
        WellFormed Γ (@Typ.box i _ T)
    | cap :
        WellFormed Γ S →
        Shape S →
        Cap.WellFormed Γ C →
        WellFormed Γ (.cap S C)

  lemma WellFormed_WellScoped :
    WellFormed Γ T →
    WellScoped T
  := by
    intros T.WF
    induction T.WF
    · case var X R Γ X.In =>
      constructor; constructor
    · case top Γ =>
      constructor
    · case arr Γ T U L T.WF U.WF T.IH U.IH =>
      constructor
      · exact T.IH
      · exact U.IH
    · case all Γ S U k L S.WF S.Shape U.WF S.WS U.IH =>
      constructor
      · exact S.WS
      · exact U.IH
    · case box Γ T _ T.WF T.IH =>
      constructor; exact T.IH
    · case cap Γ S C S.WF S.Shape C.WF S.WS =>
      constructor
      · exact S.WS
      · apply Cap.WellFormed_WellScoped C.WF

  lemma WellFormed_weaken :
    WellFormed Δ T →
    WellFormed (Γ ++ Δ) T
  := by
    rename_i i
    intros WF
    induction WF
    · case var X T Δ X.Mem =>
      apply WellFormed.var (S := T)
      apply Env.mem_tail X.Mem
    · case top => constructor
    · case arr Δ T U L T.WF U.WF T.IH U.IH =>
      apply WellFormed.arr L T.IH
      intros x x.NotIn
      rw [<- Env.concat_cons]
      exact U.IH x x.NotIn
    · case all Δ S U k L S.WF S.Shape U.WF S.IH U.IH =>
      apply WellFormed.all L S.IH S.Shape
      intros X X.NotIn
      rw [<- Env.concat_cons]
      exact U.IH X X.NotIn
    · case box Δ T _ T.WF T.IH =>
      apply WellFormed.box T.IH
    · case cap Δ S C S.WF S.Shape C.WF S.IH =>
      exact WellFormed.cap S.IH S.Shape (Cap.WellFormed_weaken C.WF)

  lemma WellFormed_weaken_head :
    a.name ∉ dom Γ →
    WellFormed Γ T →
    WellFormed (Γ ▷ a) T
  := by
    rename_i i
    intros NotIn WF
    induction WF
    · case var X T Δ X.Mem =>
      apply WellFormed.var (S := T)
      apply Env.mem_cons_tail
      · exact Γ
      · simp
        intros Eq
        cases
        apply HEq


    · case top => constructor
    · case arr Δ T U L T.WF U.WF T.IH U.IH =>
      apply WellFormed.arr L T.IH
      intros x x.NotIn
      rw [<- Env.concat_cons]
      exact U.IH x x.NotIn
    · case all Δ S U k L S.WF S.Shape U.WF S.IH U.IH =>
      apply WellFormed.all L S.IH S.Shape
      intros X X.NotIn
      rw [<- Env.concat_cons]
      exact U.IH X X.NotIn
    · case box Δ T _ T.WF T.IH =>
      apply WellFormed.box T.IH
    · case cap Δ S C S.WF S.Shape C.WF S.IH =>
      exact WellFormed.cap S.IH S.Shape (Cap.WellFormed_weaken C.WF)

  instance instWellFormedness : WellFormedness i (Typ i) where
    WellFormed := WellFormed
    WellFormed_WellScoped := WellFormed_WellScoped
    WellFormed_weaken := WellFormed_weaken
end Typ

inductive Env.WellFormed : Env i → Prop where
  | nil : Env.WellFormed ∅
  | val :
      Env.WellFormed (erase Γ x) →
      Typ.WellFormed (erase Γ x) T →
      Env.WellFormed (Γ ▷ x ⦂ T)
  | sub :
      Env.WellFormed (erase Γ X) →
      Typ.WellFormed (erase Γ X) S →
      Typ.Shape S →
      Env.WellFormed (Γ ▷ X <: S)
  | typ [HasFeature i type_bindings] :
      Env.WellFormed (erase Γ X) →
      Typ.WellFormed (erase Γ X) T →
      Env.WellFormed (Γ ▷ @Assoc.typ i _ X T)

namespace Env
  @[elab_as_elim,eliminator]
  lemma WellFormed.rec_bindings {i : CC} {motive : (Γ : Env i) → WellFormed Γ → Prop}
    (nil : motive ∅ .nil)
    (val : ∀ {Γ : Env i} {x : Atom (var i)} {T : Typ i}
             (xNotIn : x ∉ dom Γ)
             (ΓWF : WellFormed Γ)
             (TWF : Typ.WellFormed Γ T),
          motive Γ ΓWF →
          motive (Γ ▷ x ⦂ T) (.val ((Env.erase_not_in_dom xNotIn).symm ▸ ΓWF)
                                   ((Env.erase_not_in_dom xNotIn).symm ▸ TWF)))
    (sub : ∀ {Γ : Env i} {X : Atom (tvar i)} {S : Typ i}
             (XNotIn : X ∉ dom Γ)
             (ΓWF : WellFormed Γ)
             (SWF : Typ.WellFormed Γ S)
             (SShape : Typ.Shape S),
          motive Γ ΓWF →
          motive (Γ ▷ X <: S) (.sub ((Env.erase_not_in_dom XNotIn).symm ▸ ΓWF)
                                    ((Env.erase_not_in_dom XNotIn).symm ▸ SWF)
                                    SShape))
    (typ : ∀ {Γ : Env i} {X : Atom (tvar i)} {T : Typ i}
             (XNotIn : X ∉ dom Γ)
             (ΓWF : WellFormed Γ)
             (TWF : Typ.WellFormed Γ T),
          motive Γ ΓWF →
          motive (Γ ▷ X ≔ T) (.typ ((Env.erase_not_in_dom XNotIn).symm ▸ ΓWF)
                                   ((Env.erase_not_in_dom XNotIn).symm ▸ TWF)))
    : ∀ {Γ : Env i} (ΓWF : WellFormed Γ), motive Γ ΓWF
  := by
    intros Γ ΓWF
    induction Γ
    · case nil =>
      apply nil
    · case val x T Γ x.NotIn IH =>
      generalize Eq.gen : Γ ▷ x ⦂ T = Δ at ΓWF
      cases ΓWF
      · case nil => simp [Env.cons_not_nil] at Eq.gen
      · case val Γ' x' T' Γ'.WF T'.WF =>
        obtain ⟨Eq.Γ, Eq.a⟩ := Env.cons_eq_iff.mp Eq.gen
        simp [Env.erase_not_in_dom x.NotIn] at Eq.Γ
        simp at Eq.a
        obtain ⟨Eq.x, Eq.T⟩ := Eq.a
        conv =>
          lhs
          rw [<- Eq.gen]
          rfl
        rw [<- Eq.Γ] at Γ'.WF T'.WF
        rw [<- Eq.T] at T'.WF
        apply val x.NotIn Γ'.WF T'.WF (IH Γ'.WF)
      · case sub =>
        obtain ⟨Eq.Γ, Eq.a⟩ := Env.cons_eq_iff.mp Eq.gen
        simp at Eq.a
      · case typ =>
        obtain ⟨Eq.Γ, Eq.a⟩ := Env.cons_eq_iff.mp Eq.gen
        simp at Eq.a
    · case sub X S Γ X.NotIn IH =>
      generalize Eq.gen : Γ ▷ X <: S = Δ at ΓWF
      cases ΓWF
      · case nil => simp [Env.cons_not_nil] at Eq.gen
      · case val =>
        obtain ⟨Eq.Γ, Eq.a⟩ := Env.cons_eq_iff.mp Eq.gen
        simp at Eq.a
      · case sub Γ' X' S' Γ'.WF S'.WF S'.Shape =>
        obtain ⟨Eq.Γ, Eq.a⟩ := Env.cons_eq_iff.mp Eq.gen
        simp [Env.erase_not_in_dom X.NotIn] at Eq.Γ
        simp at Eq.a
        obtain ⟨Eq.X, Eq.S⟩ := Eq.a
        conv =>
          lhs
          rw [<- Eq.gen]
          rfl
        rw [<- Eq.Γ] at Γ'.WF S'.WF
        rw [<- Eq.S] at S'.WF S'.Shape
        apply sub X.NotIn Γ'.WF S'.WF S'.Shape (IH Γ'.WF)
      · case typ =>
        obtain ⟨Eq.Γ, Eq.a⟩ := Env.cons_eq_iff.mp Eq.gen
        simp at Eq.a
    · case typ X T Γ X.NotIn IH =>
      generalize Eq.gen : Γ ▷ X ≔ T = Δ at ΓWF
      cases ΓWF
      · case nil => simp [Env.cons_not_nil] at Eq.gen
      · case val =>
        obtain ⟨Eq.Γ, Eq.a⟩ := Env.cons_eq_iff.mp Eq.gen
        simp at Eq.a
      · case sub =>
        obtain ⟨Eq.Γ, Eq.a⟩ := Env.cons_eq_iff.mp Eq.gen
        simp at Eq.a
      · case typ Γ' T' X' _ Γ'.WF T'.WF =>
        obtain ⟨Eq.Γ, Eq.a⟩ := Env.cons_eq_iff.mp Eq.gen
        simp [Env.erase_not_in_dom X.NotIn] at Eq.Γ
        simp at Eq.a
        obtain ⟨Eq.X, Eq.T⟩ := Eq.a
        conv =>
          lhs
          rw [<- Eq.gen]
          rfl
        rw [<- Eq.Γ] at Γ'.WF T'.WF
        rw [<- Eq.T] at T'.WF
        apply typ X.NotIn Γ'.WF T'.WF (IH Γ'.WF)
      · case sub =>
        obtain ⟨Eq.Γ, Eq.a⟩ := Env.cons_eq_iff.mp Eq.gen
        simp at Eq.a
      · case typ =>
        obtain ⟨Eq.Γ, Eq.a⟩ := Env.cons_eq_iff.mp Eq.gen
        simp at Eq.a

  lemma WellFormed_of_mem {Γ : Env i} :
    Env.WellFormed Γ →
    a ∈ Γ →
    Typ.WellFormed Γ a.type
  := by
    intros Γ.WF a.In
    induction Γ.WF
    · case nil => simp [Env.not_mem_nil] at a.In
    all_goals {
      rename_i Γ x T x.NotIn Γ.WF T.WF Γ.IH
      simp [Env.mem_cons] at a.In
      rw [Env.erase_not_in_dom x.NotIn] at a.In
      cases a.In
      · case inl a.In =>
        apply WellFormedness.WellFormed_weaken_head
        sorry
    }
end Env

lemma Typ.WellFormed_Type :
  Env.WellFormed Γ →
  Typ.WellFormed Γ T →
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
