import CCDeconstructed.Syntax
import CCDeconstructed.Classes
import CCDeconstructed.Tactics
import CCDeconstructed.Infrastructure.Var
import CCDeconstructed.Infrastructure.Typ

set_option linter.unusedVariables false

open Scoped FreeVariables VarCat

namespace Exp
  instance : Coe (Var (.var i)) (Exp i) where
    coe := Exp.var

  @[simp]
  def fvVar (e : Exp i) : Finset (Atom (.var i)) :=
    match e with
    | .var v => v.fv
    | .abs T e => T.fvVar ∪ e.fvVar
    | .app f e => fv f ∪ fv e
    | .tabs _ T e => T.fvVar ∪ e.fvVar
    | .tapp f R => f.fv ∪ R.fvVar
    | .let_ e1 e2 => e1.fvVar ∪ e2.fvVar
    | @Exp.type _ _ T e => T.fvVar ∪ e.fvVar
    | @Exp.box _ _ x => x.fv
    | @Exp.unbox _ _ x => x.fv

  @[simp]
  def fvTyp (e : Exp i) : Finset (Atom (.tvar i)) :=
    match e with
    | .var _ => ∅
    | .abs T e => T.fvTyp ∪ e.fvTyp
    | .app _ _ => ∅
    | .tabs k T e => T.fvTyp ∪ e.fvTyp
    | .tapp _ T => T.fvTyp
    | .let_ e1 e2 => e1.fvTyp ∪ e2.fvTyp
    | @Exp.type _ _ T e => T.fvTyp ∪ e.fvTyp
    | @Exp.box _ _ _ => ∅
    | @Exp.unbox _ _ _ => ∅

  @[simp]
  instance : FreeVariables (Exp i) (.var i) where
    fv := fvVar

  @[simp]
  instance : FreeVariables (Exp i) (.tvar i) where
    fv := fvTyp

  @[aesop norm]
  def instantiateRecCap (e : Exp i) (k : Index (.var i)) (u : Var (.var i)) (D : Cap i) : Exp i :=
    match e with
    | .var v => v.instantiateRec k u
    | .abs T e => .abs (T.instantiateRecCap k D) (e.instantiateRecCap (k + 1) u D)
    | .app f e => .app (f.instantiateRec k u) (e.instantiateRec k u)
    | .tabs k' T e => .tabs k' (T.instantiateRecCap k D) (e.instantiateRecCap (k + 1) u D)
    | .tapp x T => .tapp (x.instantiateRec k u) (T.instantiateRecCap k D)
    | .let_ e1 e2 => .let_ (e1.instantiateRecCap k u D) (e2.instantiateRecCap (k + 1) u D)
    | @Exp.type _ _ T e => .type (T.instantiateRecCap k D) (e.instantiateRecCap (k + 1) u D)
    | @Exp.box _ _ x => .box (x.instantiateRec k u)
    | @Exp.unbox _ _ x => .unbox (x.instantiateRec k u)

  @[aesop norm]
  def instantiateRecVar (e : Exp i) (k : Index (.var i)) (u : Var (.var i)) : Exp i :=
    instantiateRecCap e k u {u}

  @[aesop norm]
  def substituteCap (e : Exp i) (x : Atom (.var i)) (u : Var (.var i)) (D : Cap i) : Exp i :=
    match e with
    | .var v => v.substitute x u
    | .abs T e => .abs T (e.substituteCap x u D)
    | .app f e =>.app (f.substitute x u) (e.substitute x u)
    | .tabs k T e => .tabs k (T.substituteCap x D) (e.substituteCap x u D)
    | .tapp f T => .tapp (f.substitute x u) (T.substituteCap x D)
    | .let_ e1 e2 => .let_ (e1.substituteCap x u D) (e2.substituteCap x u D)
    | @Exp.type _ _ T e => .type (T.substituteCap x D) (e.substituteCap x u D)
    | @Exp.box _ _ v => .box (v.substitute x u)
    | @Exp.unbox _ _ v => .unbox (v.substitute x u)

  @[aesop norm]
  def substituteVar (e : Exp i) (x : Atom (.var i)) (u : Var (.var i)) : Exp i :=
    substituteCap e x u {u}

  @[aesop norm]
  def instantiateRecTyp (e : Exp i) (K : Index (.tvar i)) (U : Typ i) : Exp i :=
    match e with
    | .var v => v
    | .abs T e => .abs (T.instantiateRecTyp K U) (e.instantiateRecTyp (K + 1) U)
    | .app f e =>.app f e
    | .tabs k T e => .tabs k (T.instantiateRecTyp K U) (e.instantiateRecTyp (K + 1) U)
    | .tapp f T => .tapp f (T.instantiateRecTyp K U)
    | .let_ e1 e2 => .let_ (e1.instantiateRecTyp K U) (e2.instantiateRecTyp (K + 1) U)
    | @Exp.type _ _ T e => .type (T.instantiateRecTyp K U) (e.instantiateRecTyp (K + 1) U)
    | @Exp.box _ _ x => .box x
    | @Exp.unbox _ _ x => .unbox x

  @[aesop norm]
  def substituteTyp (e : Exp i) (X : Atom (.tvar i)) (U : Typ i) : Exp i :=
    match e with
    | .var v => .var v
    | .abs T e => .abs (T.substituteTyp X U) (e.substituteTyp X U)
    | .app f e =>.app f e
    | .tabs k T e => .tabs k (T.substituteTyp X U) (e.substituteTyp X U)
    | .tapp f T => .tapp f (T.substituteTyp X U)
    | .let_ e1 e2 => .let_ (e1.substituteTyp X U) (e2.substituteTyp X U)
    | @Exp.type _ _ T e => .type (T.substituteTyp X U) (e.substituteTyp X U)
    | @Exp.box _ _ x => .box x
    | @Exp.unbox _ _ x => .unbox x

  @[aesop unsafe constructors 50%]
  inductive WellScopedRec {i : CC} : Nat → Exp i → Prop :=
    | var :
        Var.WellScopedRec (allowCap := false) n v →
        WellScopedRec n (.var v)
    | abs :
        Typ.WellScopedRec n T →
        WellScopedRec (n + 1) e →
        WellScopedRec n (.abs T e)
    | app :
        Var.WellScopedRec (allowCap := false) n f →
        Var.WellScopedRec (allowCap := false) n e →
        WellScopedRec n (.app f e)
    | tabs :
        Typ.WellScopedRec n T →
        WellScopedRec (n + 1) e →
        WellScopedRec n (.tabs k T e)
    | tapp :
        Var.WellScopedRec (allowCap := false) n f →
        Typ.WellScopedRec n T →
        WellScopedRec n (.tapp f T)
    | let_ :
        WellScopedRec n e1 →
        WellScopedRec (n + 1) e2 →
        WellScopedRec n (.let_ e1 e2)
    | type [HasFeature i .type_bindings] :
       Typ.WellScopedRec n T →
       WellScopedRec (n + 1) e →
       WellScopedRec n (.type T e)
    | box [HasFeature i .explicit_boxing] :
       Var.WellScopedRec (allowCap := false) n v →
       WellScopedRec n (.box v)
    | unbox [HasFeature i .explicit_boxing] :
       Var.WellScopedRec (allowCap := false) n v →
      WellScopedRec n (.unbox v)

  @[aesop unsafe constructors 50%]
  inductive WellScoped {i : CC} : Exp i → Prop :=
    | var :
        Var.WellScoped (allowCap := false) v →
        WellScoped (.var v)
    | abs (L : Finset (Atom (.var i))) :
        Typ.WellScoped T →
        (∀ x ∉ L, WellScoped (e.instantiateRecVar 0 x)) →
        WellScoped (.abs T e)
    | app :
        Var.WellScoped (allowCap := false) f →
        Var.WellScoped (allowCap := false) e →
        WellScoped (.app f e)
    | tabs (L : Finset (Atom (.tvar i))) :
        Typ.WellScoped T →
        (∀ X ∉ L, WellScoped (e.instantiateRecTyp 0 X)) →
        WellScoped (.tabs k T e)
    | tapp :
        Var.WellScoped (allowCap := false) f →
        Typ.WellScoped T →
        WellScoped (.tapp f T)
    | let_ (L : Finset (Atom (.var i))) :
        WellScoped e1 →
        (∀ x ∉ L, WellScoped (e2.instantiateRecVar 0 x)) →
        WellScoped (.let_ e1 e2)
    | type [HasFeature i .type_bindings] (L : Finset (Atom (.tvar i))) :
        Typ.WellScoped T →
        (∀ X ∉ L, WellScoped (e.instantiateRecTyp 0 X)) →
        WellScoped (.type T e)
    | box [HasFeature i .explicit_boxing] :
        Var.WellScoped (allowCap := false) v →
        WellScoped (.box v)
    | unbox [HasFeature i .explicit_boxing] :
        Var.WellScoped (allowCap := false) v →
        WellScoped (.unbox v)

  @[aesop unsafe]
  lemma WellScopedRec_instantiateRecTyp :
    WellScopedRec n (e.instantiateRecTyp n U) →
    WellScopedRec (n + 1) e
  := by
    intros e.WS
    generalize Eq : instantiateRecTyp e n U = e'
    rw [Eq] at e.WS
    induction' e.WS generalizing e U
    · case var n v v.WS =>
      cases e <;> simp [instantiateRecTyp] at Eq
      case var w =>
      rw [Eq] at *
      constructor
      apply Var.WellScoped.weaken (m := n)
      · linarith
      · assumption
    · case abs n T e1 T.WS _ e1.IH =>
      cases e <;> simp [instantiateRecTyp] at Eq
      case abs T' e' =>
      rw [<- Eq.1] at T.WS
      constructor
      · apply Typ.WellScopedRec_instantiateRecTyp (U := U)
        assumption
      · apply e1.IH (U := U)
        exact Eq.2
    · case app n f e f.WS e.WS =>
      cases e <;> simp [instantiateRecTyp] at Eq
      case app n f' e' =>
      constructor
        <;> apply Var.WellScoped.weaken (m := n) (by linarith)
        <;> rw [Eq.1,Eq.2] at *
        <;> assumption
    · case tabs n T e1 k T.WS _ e1.IH =>
      cases e <;> simp [instantiateRecTyp] at Eq
      case tabs k' T' e1' =>
      obtain ⟨Eq.k, ⟨Eq.T, Eq.e1⟩⟩ := Eq
      rw [<- Eq.T] at T.WS
      constructor
      · apply Typ.WellScopedRec_instantiateRecTyp (U := U)
        assumption
      · apply e1.IH (U := U)
        exact Eq.e1
    · case tapp n f T f.WS T.WS =>
      cases e <;> simp [instantiateRecTyp] at Eq
      case tapp n f' T' =>
      constructor
      · apply Var.WellScoped.weaken (m := n) (by linarith)
        rw [Eq.1]
        assumption
      · apply Typ.WellScopedRec_instantiateRecTyp (U := U)
        rw [Eq.2]
        assumption
    · case let_ n _ _ e1.WS e2.WS =>
      cases e <;> simp [instantiateRecTyp] at Eq
      case let_ n e1' e2' =>
      constructor
      · apply e1.WS Eq.1
      · apply e2.WS Eq.2
    · case type T e _ T.WS e.WS e.IH =>
      cases e <;> simp [instantiateRecTyp] at Eq
      case type T' e' =>
      constructor
      · apply Typ.WellScopedRec_instantiateRecTyp (U := U)
        rw [Eq.1]
        assumption
      · apply e.IH (U := U)
        exact Eq.2
    · case box n v _ v.WS =>
      cases e <;> simp [instantiateRecTyp] at Eq
      case box w =>
      rw [Eq] at *
      constructor
      apply Var.WellScoped.weaken (m := n) (by linarith) v.WS
    · case unbox n v _ v.WS =>
      cases e <;> simp [instantiateRecTyp] at Eq
      case unbox w =>
      rw [Eq] at *
      constructor
      apply Var.WellScoped.weaken (m := n) (by linarith) v.WS

  @[aesop unsafe]
  lemma WellScopedRec_instantiateRecCap :
    WellScopedRec n (instantiateRecCap e n u D) →
    WellScopedRec (n + 1) e
  := by
    intros e.WS
    generalize Eq : instantiateRecCap e n u D = e'
    rw [Eq] at e.WS
    induction' e.WS generalizing e
    · case var n v v.WS =>
      cases e <;> simp [instantiateRecCap] at Eq
      case var w =>
      constructor
      apply Var.WellScopedRec_instantiateRec (u := u)
      rw [<- Eq] at v.WS
      exact v.WS
    · case abs n T e1 T.WS _ e1.IH =>
      cases e <;> simp [instantiateRecCap] at Eq
      case abs T' e' =>
      rw [<- Eq.1] at T.WS
      constructor
      · apply Typ.WellScopedRec_instantiateRecCap T.WS
      · apply e1.IH
        exact Eq.2
    · case app n f e f.WS e.WS =>
      cases e <;> simp [instantiateRecCap,-Var.instantiateRec] at Eq
      case app n f' e' =>
      constructor
        <;> apply Var.WellScopedRec_instantiateRec (u := u)
        <;> rw [Eq.1,Eq.2] at *
        <;> assumption
    · case tabs n T e1 k T.WS _ e1.IH =>
      cases e <;> simp [instantiateRecCap] at Eq
      case tabs k' T' e1' =>
      obtain ⟨Eq.k, ⟨Eq.T, Eq.e1⟩⟩ := Eq
      constructor
      · apply Typ.WellScopedRec_instantiateRecCap
        rw [Eq.T]
        exact T.WS
      · apply e1.IH
        exact Eq.e1
    · case tapp n f T f.WS T.WS =>
      cases e <;> simp [instantiateRecCap,-Var.instantiateRec] at Eq
      case tapp n f' T' =>
      constructor
      · apply Var.WellScopedRec_instantiateRec (u := u)
        rw [Eq.1]
        exact f.WS
      · apply Typ.WellScopedRec_instantiateRecCap
        rw [Eq.2]
        exact T.WS
    · case let_ n _ _ e1.WS e2.WS =>
      cases e <;> simp [instantiateRecCap] at Eq
      case let_ e1' e2' =>
      constructor
      · apply e1.WS Eq.1
      · apply e2.WS Eq.2
    · case type n _ _ _ T.WS e.WS e.IH =>
      cases e <;> simp [instantiateRecCap] at Eq
      case type T' e' =>
      constructor
      · apply Typ.WellScopedRec_instantiateRecCap
        rw [Eq.1]
        exact T.WS
      · apply e.IH
        exact Eq.2
    · case box n _ _ v.WS =>
      cases e <;> simp [instantiateRecCap,-Var.instantiateRec] at Eq
      case box w =>
      constructor
      apply Var.WellScopedRec_instantiateRec (u := u)
      rw [Eq]
      exact v.WS
    · case unbox n _ _ v.WS =>
      cases e <;> simp [instantiateRecCap,-Var.instantiateRec] at Eq
      case unbox w =>
      constructor
      apply Var.WellScopedRec_instantiateRec (u := u)
      rw [Eq]
      exact v.WS

  @[aesop unsafe]
  lemma WellScopedRec_instantiateRecVar :
    WellScopedRec n (instantiateRecVar e n u) →
    WellScopedRec (n + 1) e
  := WellScopedRec_instantiateRecCap

  namespace WellScoped
    @[aesop unsafe]
    lemma WellScopedRec0 :
      WellScoped e →
      WellScopedRec 0 e
    := by
      intros WS
      induction' WS <;> constructor <;> aesop

    @[aesop unsafe]
    lemma weaken :
      m <= n →
      WellScopedRec m e→
      WellScopedRec n e
    := by
      intros leq WS
      induction' WS generalizing n
      · case var m v v.WS =>
        constructor
        apply Var.WellScoped.weaken (m := m) leq v.WS
      · case abs m T e T.WS e.WS e.IH =>
        constructor
        · apply Typ.WellScoped.weaken (m := m) leq T.WS
        · apply e.IH; linarith
      · case app m f e f.WS e.WS =>
        constructor
          <;> apply Var.WellScoped.weaken (m := m) leq
          <;> assumption
      · case tabs m T e k T.WS e.WS e.IH =>
        constructor
        · apply Typ.WellScoped.weaken (m := m) leq T.WS
        · apply e.IH; linarith
      · case tapp m f T f.WS T.WS =>
        constructor
        · apply Var.WellScoped.weaken (m := m) leq f.WS
        · apply Typ.WellScoped.weaken (m := m) leq T.WS
      · case let_ m e1 e2 e1.WS e2.WS e1.IH e2.IH =>
        constructor
        · apply e1.IH leq
        · apply e2.IH (n := n + 1); linarith
      · case type m T e _ T.WS e.WS e.IH =>
        constructor
        · apply Typ.WellScoped.weaken (m := m) leq T.WS
        · apply e.IH (n := n + 1); linarith
      · case box m v _ v.WS =>
        constructor
        apply Var.WellScoped.weaken (m := m) leq v.WS
      · case unbox m v _ v.WS =>
        constructor
        apply Var.WellScoped.weaken (m := m) leq v.WS

    @[simp]
    instance instWellScopedness : WellScopedness (Exp i) where
      WellScopedRec := WellScopedRec
      WellScoped := WellScoped

    @[simp]
    instance instWellScopednessInfrastructure : WellScopedness.Infrastructure (Exp i) where
      WellScopedRec0 := WellScopedRec0
      weaken := weaken
  end WellScoped

  @[aesop unsafe]
  lemma substituteCap_fresh :
    x ∉ fvVar e →
    substituteCap e x u D = e
  := by
    intros x.NotIn
    induction e <;> aesop

  @[aesop unsafe]
  lemma substituteVar_fresh :
    x ∉ fvVar e →
    substituteVar e x u = e
  := substituteCap_fresh

  @[aesop unsafe]
  lemma instantiateRecCap_WellScopedRec :
    WellScopedRec n e →
    k >= n →
    instantiateRecCap e k u D = e
  := by
    intros WS geq
    induction WS generalizing k <;> simp [instantiateRecCap,-Var.instantiateRec]
    · case var v v.WS =>
      apply Var.instantiateRec_WellScopedRec v.WS geq
    · case abs T e T.WS e.WS e.IH =>
      aesop
    · case app f e f.WS e.WS =>
      apply And.intro
        <;> apply Var.instantiateRec_WellScopedRec
        <;> assumption
    · case tabs T e T.WS e.WS e.IH =>
      apply And.intro
      · exact Typ.instantiateRecVar_WellScopedRec T.WS geq
      · apply e.IH (k := k + 1)
        linarith
    · case tapp f T f.WS T.WS =>
      apply And.intro
      · apply Var.instantiateRec_WellScopedRec <;> assumption
      · apply Typ.instantiateRecVar_WellScopedRec T.WS geq
    · case let_ e1 e2 e1.WS e2.WS e1.IH e2.IH =>
      aesop
    · case type T e T.WS e.WS e.IH =>
      aesop
    · case box v v.WS =>
      apply Var.instantiateRec_WellScopedRec v.WS geq
    · case unbox v v.WS =>
      apply Var.instantiateRec_WellScopedRec v.WS geq

  @[aesop unsafe]
  lemma instantiateRecVar_WellScopedRec :
    WellScopedRec n e →
    k >= n →
    instantiateRecVar e k u = e
  := instantiateRecCap_WellScopedRec

  @[simp]
  instance instScopedVar : Scoped (Exp i) (.var i) where
    instantiateRec := instantiateRecVar
    substitute := substituteVar

  @[simp]
  instance instScopedInfrastructureVar : Scoped.Infrastructure (Exp i) (.var i) where
    substitute_fresh := substituteVar_fresh
    instantiateRec_WellScopedRec := instantiateRecVar_WellScopedRec
    WellScopedRec_instantiateRec := WellScopedRec_instantiateRecVar

  @[aesop safe forward]
  lemma substituteTyp_fresh :
    X ∉ fvTyp e →
    substituteTyp e X U = e
  := by
    intros x.NotIn
    induction e <;> simp [fvTyp] at x.NotIn <;> simp [substituteTyp]
    · case abs T e e.IH =>
      apply And.intro
      . apply Typ.substituteTyp_fresh (by aesop)
      · apply e.IH (by aesop)
    · case tabs T e e.WS e.IH =>
      apply And.intro
      · apply Typ.substituteTyp_fresh (by aesop)
      · apply e.IH (by aesop)
    · case tapp f T =>
      apply Typ.substituteTyp_fresh (by aesop)
    · case let_ e1 e2 e1.IH e2.IH =>
      apply And.intro
      . apply e1.IH (by aesop)
      · apply e2.IH (by aesop)
    · case type T e T.WS e.WS e.IH =>
      apply And.intro
      · apply Typ.substituteTyp_fresh (by aesop)
      · apply e.IH (by aesop)

  @[aesop safe forward]
  lemma instantiateRecTyp_WellScopedRec :
    WellScopedRec n e →
    k >= n →
    instantiateRecTyp e k U = e
  := by
    intros WS geq
    induction WS generalizing k <;> simp [instantiateRecTyp] <;> aesop

  instance instScopedTyp : Scoped (Exp i) (.tvar i) where
    instantiateRec := instantiateRecTyp
    substitute := substituteTyp

  instance instScopedInfrastructureTyp : Scoped.Infrastructure (Exp i) (.tvar i) where
    substitute_fresh := substituteTyp_fresh
    WellScopedRec_instantiateRec := WellScopedRec_instantiateRecTyp
    instantiateRec_WellScopedRec := instantiateRecTyp_WellScopedRec
end Exp
