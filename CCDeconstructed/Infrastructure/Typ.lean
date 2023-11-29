import CCDeconstructed.Syntax
import CCDeconstructed.Classes
import CCDeconstructed.Tactics
import CCDeconstructed.Infrastructure.Var
import CCDeconstructed.Infrastructure.Cap

set_option linter.unusedVariables false

open Scoped FreeVariables VarCat

namespace Typ
  instance : Coe (Var (.tvar i)) (Typ i) where
    coe := Typ.var

  @[aesop norm]
  def freeVariablesTyp (T : Typ i) : Finset (Atom (.tvar i)) :=
    match T with
    | .top => ∅
    | .var V => fv V
    | .arr A B => A.freeVariablesTyp ∪ B.freeVariablesTyp
    | .all _ A B => A.freeVariablesTyp ∪ B.freeVariablesTyp
    | @Typ.box _ _ A => A.freeVariablesTyp
    | .cap S _ => S.freeVariablesTyp

  @[aesop norm]
  def freeVariablesVar (T : Typ i) : Finset (Atom (.var i)) :=
    match T with
    | .top => ∅
    | .var _ => ∅
    | .arr A B => A.freeVariablesVar ∪ B.freeVariablesVar
    | .all _ A B => A.freeVariablesVar ∪ B.freeVariablesVar
    | @Typ.box _ _ A => A.freeVariablesVar
    | .cap S C => S.freeVariablesVar ∪ fv C

  instance instFreeVariablesVar : FreeVariables (Typ i) (.var i) where
    fv := freeVariablesVar

  instance instFreeVariablesTVar : FreeVariables (Typ i) (.tvar i) where
    fv := freeVariablesTyp

  @[aesop norm]
  def instantiateRecTyp (T : Typ i) (K : Index (tvar i)) (U : Typ i) : Typ i :=
    match T with
    | .top => .top
    | .var V => V.subst K U
    | .arr A B => .arr (A.instantiateRecTyp K U) (B.instantiateRecTyp (K + 1) U)
    | .all k A B => .all k (A.instantiateRecTyp K U) (B.instantiateRecTyp (K + 1) U)
    | Typ.box A => .box (A.instantiateRecTyp K U)
    | .cap S C => .cap (S.instantiateRecTyp K U) C

  @[aesop norm]
  def substituteTyp (T : Typ i) (X : Atom (.tvar i)) (U : Typ i) : Typ i :=
    match T with
    | .top => .top
    | .var V => V.subst X U
    | .arr A B => .arr (A.substituteTyp X U) (B.substituteTyp X U)
    | .all k A B => .all k (A.substituteTyp X U) (B.substituteTyp X U)
    | @Typ.box _ _ A => .box (A.substituteTyp X U)
    | .cap S C => .cap (S.substituteTyp X U) C

  @[aesop norm]
  def instantiateRecVar (T : Typ i) (k : Index (.var i)) (u : Var (.var i)) : Typ i :=
    match T with
    | .top => .top
    | .var V => V
    | .arr A B => .arr (A.instantiateRecVar k u) (B.instantiateRecVar (k + 1) u)
    | .all k' A B => .all k' (A.instantiateRecVar k u) (B.instantiateRecVar (k + 1) u)
    | Typ.box A => .box (A.instantiateRecVar k u)
    | .cap S C => .cap (S.instantiateRecVar k u) (C.instantiateRec k u)

  @[aesop norm]
  def substituteVar (T : Typ i) (x : Atom (.var i)) (u : Var (.var i)) : Typ i :=
    match T with
    | .top => .top
    | .var V => V
    | .arr A B => .arr (A.substituteVar x u) (B.substituteVar x u)
    | .all k' A B => .all k' (A.substituteVar x u) (B.substituteVar x u)
    | @Typ.box _ _ A => .box (A.substituteVar x u)
    | .cap S C => .cap (S.substituteVar x u) (C.substitute x u)

  @[aesop unsafe [constructors 50%]]
  inductive WellScopedRec {i : CC} : Nat → Typ i → Prop :=
    | top : WellScopedRec n .top
    | var : Var.WellScopedRec (allowCap := false) n V → WellScopedRec n (.var V)
    | arr :
        WellScopedRec n A →
        WellScopedRec (n + 1) B →
        WellScopedRec n (.arr A B)
    | all :
        WellScopedRec n A →
        WellScopedRec (n + 1) B →
        WellScopedRec n (.all k A B)
    | box [HasFeature i .box_type] :
        WellScopedRec n T →
        WellScopedRec n (.box T)
    | cap :
       WellScopedRec n S →
       Cap.WellScopedRec n C →
       WellScopedRec n (.cap S C)

  @[aesop unsafe [constructors 50%]]
  inductive WellScoped {i : CC} : Typ i → Prop :=
    | top : WellScoped .top
    | var : Var.WellScoped (allowCap := false) V → WellScoped (.var V)
    | arr (L : Finset (Atom (.var i))) :
        WellScoped T →
        (∀ (x : Atom (.var i)), x ∉ L → WellScoped (U.instantiateRecVar 0 (.free x))) →
        WellScoped (.arr T U)
    | all (L : Finset (Atom (tvar i))) :
        WellScoped S →
        (∀ (X : Atom (.tvar i)), X ∉ L → WellScoped (U.instantiateRecTyp 0 (Typ.var X))) →
        WellScoped (.all k S U)
    | box [HasFeature i .box_type] :
        WellScoped T →
        WellScoped (.box T)
    | cap :
       WellScoped S →
       WellScopedness.WellScoped C →
       WellScoped (.cap S C)

  @[aesop safe forward]
  lemma WellScopedRec_instantiateRecTyp :
    WellScopedRec n (instantiateRecTyp T n U) →
    WellScopedRec (n + 1) T
  := by
    intros T.WS
    generalize Eq : instantiateRecTyp T n U = T'
    rw [Eq] at T.WS
    induction' T.WS generalizing T
    all_goals cases T
      <;> simp only [instantiateRecTyp] at Eq
      <;> constructor
      <;> simp [Index] at *
      <;> aesop
    · linarith
    . rename_i V K
      suffices K < n_1 by simp [Index] at *; linarith
      apply a_1 (.bound K) a_4

  @[aesop safe forward]
  lemma WellScopedRec_instantiateRecVar :
    WellScopedRec n (instantiateRecVar T n u) →
    WellScopedRec (n + 1) T
  := by
    intros T.WS
    generalize Eq : instantiateRecVar T n u = T'
    rw [Eq] at T.WS
    induction' T.WS generalizing T
    · case top n =>
      cases T <;> simp only [instantiateRecVar] at Eq; constructor
    · case var n V V.WS =>
      cases T <;> simp only [instantiateRecVar] at Eq; constructor
      apply Var.WellScopedRec_weaken (m := n) <;> aesop
    · case arr =>
      cases T <;> simp only [instantiateRecVar] at Eq; constructor <;> aesop
    · case all =>
      cases T <;> simp only [instantiateRecVar] at Eq; constructor <;> aesop
    · case box =>
      cases T <;> simp only [instantiateRecVar] at Eq; constructor; aesop
    · case cap n S C S.WS C.WS S.IH =>
      cases T <;> simp only [instantiateRecVar] at Eq
      rename_i S' C'
      injection Eq with Eq.S Eq.C
      constructor
      · apply S.IH; aesop
      · apply Cap.WellScopedRec_instantiateRec (u := u)
        rw [Eq.C]
        exact C.WS

  attribute [-aesop] specializeAnyScope
  attribute [aesop unsafe tactic 80%] specializeAnyScope

  @[aesop safe forward]
  lemma WellScoped_implies_WellScopedRec_0 :
    WellScoped T →
    WellScopedRec 0 T
  := by
    intros WS
    induction WS <;> constructor <;> aesop

  @[aesop safe forward]
  lemma WellScopedRec_weaken :
    m <= n →
    WellScopedRec m T →
    WellScopedRec n T
  := by
    intros leq WS
    induction' WS generalizing n <;> constructor <;> aesop
    linarith

  instance instWellScopedness : WellScopedness (Typ i) where
    WellScopedRec := WellScopedRec
    WellScoped := WellScoped
    WellScoped_implies_WellScopedRec_0 := WellScoped_implies_WellScopedRec_0
    WellScopedRec_weaken := WellScopedRec_weaken

  @[aesop safe forward]
  lemma substituteTyp_fresh :
    X ∉ freeVariablesTyp T →
    substituteTyp T X U = T
  := by induction T <;> aesop

  @[aesop safe forward]
  lemma instantiateRecTyp_WellScopedRec :
    WellScopedRec n T →
    K >= n →
    instantiateRecTyp T K U = T
  := by
    intros WS geq
    induction WS generalizing K <;> aesop
    exfalso; linarith

  instance instScoped : Scoped (Typ i) (tvar i) where
    instantiateRec := instantiateRecTyp
    substitute := substituteTyp
    substitute_fresh := substituteTyp_fresh
    instantiateRec_WellScopedRec := instantiateRecTyp_WellScopedRec
    WellScopedRec_instantiateRec := WellScopedRec_instantiateRecTyp

  @[aesop safe forward]
  lemma substituteVar_fresh :
    x ∉ freeVariablesVar T →
    substituteVar T x u = T
  := by
    intros x.NotIn
    induction T <;> simp [substituteVar]
    · case arr T U T.IH U.IH =>
      apply And.intro <;> aesop
    · case all S U S.IH U.IH =>
      apply And.intro <;> aesop
    · case box T T.IH =>
      apply T.IH x.NotIn
    · case cap S C S.IH =>
      apply And.intro
      · aesop
      · apply Cap.substitute_fresh
        aesop

  @[aesop safe forward]
  lemma instantiateRecVar_WellScopedRec :
    WellScopedRec n T →
    k >= n →
    instantiateRecVar T k u = T
  := by
    intros WS geq
    induction WS generalizing k <;> aesop

  instance : Scoped (Typ i) (.var i) where
    instantiateRec := instantiateRecVar
    substitute := substituteVar
    substitute_fresh := substituteVar_fresh
    WellScopedRec_instantiateRec := WellScopedRec_instantiateRecVar
    instantiateRec_WellScopedRec := instantiateRecVar_WellScopedRec
end Typ
