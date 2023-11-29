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

  @[aesop norm]
  def freeVariablesVar (e : Exp i) : Finset (Atom (.var i)) :=
    match e with
    | .var v => v.fv
    | .abs _ e => e.freeVariablesVar
    | .app f e => f.fv ∪ e.fv
    | .tabs _ e => e.freeVariablesVar
    | .tapp f _ => f.fv
    | .let_ e1 e2 => e1.freeVariablesVar ∪ e2.freeVariablesVar
    | @Exp.type _ _ _ e => e.freeVariablesVar
    | @Exp.box _ _ x => x.fv
    | @Exp.unbox _ _ x => x.fv

  @[aesop norm]
  def freeVariablesTyp (e : Exp i) : Finset (Atom (.tvar i)) :=
    match e with
    | .var _ => ∅
    | .abs T e => T.freeVariablesTyp ∪ e.freeVariablesTyp
    | .app _ _ => ∅
    | .tabs T e => T.freeVariablesTyp ∪ e.freeVariablesTyp
    | .tapp _ T => T.freeVariablesTyp
    | .let_ e1 e2 => e1.freeVariablesTyp ∪ e2.freeVariablesTyp
    | @Exp.type _ _ T e => T.freeVariablesTyp ∪ e.freeVariablesTyp
    | @Exp.box _ _ _ => ∅
    | @Exp.unbox _ _ _ => ∅

  instance : FreeVariables (Exp i) (.var i) where
    fv := freeVariablesVar

  instance : FreeVariables (Exp i) (.tvar i) where
    fv := freeVariablesTyp

  @[aesop norm]
  def instantiateRecVar (e : Exp i) (k : Index (.var i)) (u : Var (.var i)) : Exp i :=
    match e with
    | .var v => v.instantiateRec k u
    | .abs T e => .abs T (e.instantiateRecVar (k + 1) u)
    | .app f e => .app (f.instantiateRec k u) (e.instantiateRec k u)
    | .tabs T e => .tabs T (e.instantiateRecVar (k + 1) u)
    | .tapp x T => .tapp (x.instantiateRec k u) T
    | .let_ e1 e2 => .let_ (e1.instantiateRecVar k u) (e2.instantiateRecVar (k + 1) u)
    | @Exp.type _ _ T e => .type T (e.instantiateRecVar (k + 1) u)
    | @Exp.box _ _ x => .box (x.instantiateRec k u)
    | @Exp.unbox _ _ x => .unbox (x.instantiateRec k u)

  @[aesop norm]
  def substituteVar (e : Exp i) (x : Atom (.var i)) (u : Var (.var i)) : Exp i :=
    match e with
    | .var v => v.substitute x u
    | .abs T e => .abs T (e.substituteVar x u)
    | .app f e =>.app (f.substitute x u) (e.substitute x u)
    | .tabs T e => .tabs T (e.substituteVar x u)
    | .tapp f T => .tapp (f.substitute x u) T
    | .let_ e1 e2 => .let_ (e1.substituteVar x u) (e2.substituteVar x u)
    | @Exp.type _ _ T e => .type T (e.substituteVar x u)
    | @Exp.box _ _ v => .box (v.substitute x u)
    | @Exp.unbox _ _ v => .unbox (v.substitute x u)

  @[aesop norm]
  def instantiateRecTyp (e : Exp i) (K : Index (.tvar i)) (U : Typ i) : Exp i :=
    match e with
    | .var v => v
    | .abs T e => .abs (T.instantiateRecTyp K U) (e.instantiateRecTyp (K + 1) U)
    | .app f e =>.app f e
    | .tabs T e => .tabs (T.instantiateRecTyp K U) (e.instantiateRecTyp (K + 1) U)
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
    | .tabs T e => .tabs (T.substituteTyp X U) (e.substituteTyp X U)
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
        WellScopedRec n (.tabs T e)
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
        WellScoped (.tabs T e)
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

  @[elab_as_elim]
  lemma WellScoped.locally_nameless_rec {i : CC}
    {motive : ∀ (e : Exp i), WellScoped e → Prop}
    (var : ∀ (x : Atom (.var i)), motive (.var x) (.var True.intro))
    (abs : ∀ (T : Typ i) (e : Exp i) (L : Finset (Atom (.var i))) (x : Atom (.var i)) (xFresh : x ∉ L ∪ Typ.freeVariablesVar T ∪ freeVariablesVar e),
      ∀ (TWS : Typ.WellScoped T)
        (eWS : ∀ x ∉ L, WellScoped (e.instantiateRecVar 0 x))
        (eIH : motive (instantiateRecVar e 0 x) (eWS x (by aesop))),
      motive (.abs T e) (.abs L TWS eWS))
    (app : ∀ (f e : Atom (.var i)),
      motive (.app f e) (.app True.intro True.intro))
    (tabs : ∀ (T : Typ i) (e : Exp i) (L : Finset (Atom (.tvar i))) (X : Atom (.tvar i)) (XFresh : X ∉ L ∪ Typ.freeVariablesTyp T ∪ freeVariablesTyp e),
      ∀ (TWS : Typ.WellScoped T)
        (eWS : ∀ X ∉ L, WellScoped (e.instantiateRecTyp 0 X))
        (eIH : motive (instantiateRecTyp e 0 X) (eWS X (by aesop))),
      motive (.tabs T e) (.tabs L TWS eWS))
    (tapp : ∀ (f : Atom (.var i)) (T : Typ i),
      ∀ (TWS : Typ.WellScoped T),
      motive (.tapp f T) (.tapp True.intro TWS))
    (let_ : ∀ (e1 : Exp i) (e2 : Exp i) (L : Finset (Atom (.var i))) (x : Atom (.var i)) (xFresh : x ∉ L ∪ freeVariablesVar e1 ∪ freeVariablesVar e2),
      ∀ (e1WS : WellScoped e1)
        (e2WS : ∀ x ∉ L, WellScoped (e2.instantiateRecVar 0 x))
        (e1IH : motive e1 e1WS)
        (e2IH : motive (instantiateRecVar e2 0 x) (e2WS x (by aesop))),
      motive (.let_ e1 e2) (.let_ L e1WS e2WS))
    (type : ∀ [HasFeature i .type_bindings] (T : Typ i) (e : Exp i) (L : Finset (Atom (.tvar i))) (X : Atom (.tvar i)) (XFresh : X ∉ L ∪ Typ.freeVariablesTyp T ∪ freeVariablesTyp e),
      ∀ (TWS : Typ.WellScoped T)
        (eWS : ∀ X ∉ L, WellScoped (e.instantiateRecTyp 0 X))
        (eIH : motive (e.instantiateRecTyp 0 X) (eWS X (by aesop))),
      motive (.type T e) (.type L TWS eWS))
    (box : ∀ [HasFeature i .explicit_boxing] (x : Atom (.var i)),
      motive (.box x) (.box True.intro))
    (unbox : ∀ [HasFeature i .explicit_boxing] (x : Atom (.var i)),
      motive (.unbox x) (.unbox True.intro))
    : ∀ {e} WS, motive e WS
  := by
    intros e e.WS
    induction e.WS
    · case var v v.WS =>
      cases v <;> simp [Var.WellScoped] at v.WS; apply var
    · case abs T e L T.WS e.WS e.IH =>
      pick_fresh x : .var i
      apply abs T e _ x
      · apply T.WS
      · apply e.IH
      · clear * - x.Fresh; aesop
    · case app f e f.WS e.WS =>
      cases f <;> cases e <;> simp [Var.WellScoped] at f.WS e.WS
      rename_i f e
      apply app
    · case tabs T e L T.WS e.WS e.IH =>
      pick_fresh X : .tvar i
      apply tabs T e _ X
      · apply T.WS
      · apply e.IH
      · clear * - X.Fresh; aesop
    · case tapp f T f.WS T.WS =>
      cases f <;> simp [Var.WellScoped] at f.WS
      rename_i f
      apply tapp
      exact T.WS
    · case let_ e1 e2 L e1.WS e2.WS e1.IH e2.IH =>
      pick_fresh x : .var i
      apply let_ e1 e2 _ x
      · apply e1.IH
      · apply e2.IH
      · clear * - x.Fresh; aesop
    · case type T e _ L T.WS e.WS e.IH =>
      pick_fresh X : .tvar i
      apply type T e _ X
      · apply T.WS
      · apply e.IH
      · clear * - X.Fresh; aesop
    · case box v _ v.WS =>
      cases v <;> simp [Var.WellScoped] at v.WS
      rename_i x
      apply box
    · case unbox v _ v.WS =>
      cases v <;> simp [Var.WellScoped] at v.WS
      rename_i x
      apply unbox

  @[aesop safe forward]
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
      apply Var.WellScopedRec_weaken (m := n)
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
        <;> apply Var.WellScopedRec_weaken (m := n) (by linarith)
        <;> rw [Eq.1,Eq.2] at *
        <;> assumption
    · case tabs n T e1 T.WS _ e1.IH =>
      cases e <;> simp [instantiateRecTyp] at Eq
      case tabs T' e' =>
      rw [<- Eq.1] at T.WS
      constructor
      · apply Typ.WellScopedRec_instantiateRecTyp (U := U)
        assumption
      · apply e1.IH (U := U)
        exact Eq.2
    · case tapp n f T f.WS T.WS =>
      cases e <;> simp [instantiateRecTyp] at Eq
      case tapp n f' T' =>
      constructor
      · apply Var.WellScopedRec_weaken (m := n) (by linarith)
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
      apply Var.WellScopedRec_weaken (m := n) (by linarith) v.WS
    · case unbox n v _ v.WS =>
      cases e <;> simp [instantiateRecTyp] at Eq
      case unbox w =>
      rw [Eq] at *
      constructor
      apply Var.WellScopedRec_weaken (m := n) (by linarith) v.WS

  @[aesop safe forward]
  lemma WellScopedRec_instantiateRecVar :
    WellScopedRec n (instantiateRecVar e n u) →
    WellScopedRec (n + 1) e
  := by
    intros e.WS
    generalize Eq : instantiateRecVar e n u = e'
    rw [Eq] at e.WS
    induction' e.WS generalizing e
    · case var n v v.WS =>
      cases e <;> simp [instantiateRecVar] at Eq
      case var w =>
      constructor
      apply Var.WellScopedRec_instantiateRec (u := u)
      rw [<- Eq] at v.WS
      exact v.WS
    · case abs n T e1 T.WS _ e1.IH =>
      cases e <;> simp [instantiateRecVar] at Eq
      case abs T' e' =>
      rw [<- Eq.1] at T.WS
      constructor
      · apply Typ.WellScopedRec_weaken (m := n) (by linarith) T.WS
      · apply e1.IH
        exact Eq.2
    · case app n f e f.WS e.WS =>
      cases e <;> simp [instantiateRecVar] at Eq
      case app n f' e' =>
      constructor
        <;> apply Var.WellScopedRec_instantiateRec (u := u)
        <;> rw [Eq.1,Eq.2] at *
        <;> assumption
    · case tabs n T e1 T.WS _ e1.IH =>
      cases e <;> simp [instantiateRecVar] at Eq
      case tabs T' e' =>
      constructor
      · apply Typ.WellScopedRec_weaken (m := n) (by linarith)
        rw [Eq.1]
        exact T.WS
      · apply e1.IH
        exact Eq.2
    · case tapp n f T f.WS T.WS =>
      cases e <;> simp [instantiateRecVar] at Eq
      case tapp n f' T' =>
      constructor
      · apply Var.WellScopedRec_instantiateRec (u := u)
        rw [Eq.1]
        exact f.WS
      · apply Typ.WellScopedRec_weaken (m := n) (by linarith)
        rw [Eq.2]
        exact T.WS
    · case let_ n _ _ e1.WS e2.WS =>
      cases e <;> simp [instantiateRecVar] at Eq
      case let_ e1' e2' =>
      constructor
      · apply e1.WS Eq.1
      · apply e2.WS Eq.2
    · case type n _ _ _ T.WS e.WS e.IH =>
      cases e <;> simp [instantiateRecVar] at Eq
      case type T' e' =>
      constructor
      · apply Typ.WellScopedRec_weaken (m := n) (by linarith)
        rw [Eq.1]
        exact T.WS
      · apply e.IH
        exact Eq.2
    · case box n _ _ v.WS =>
      cases e <;> simp [instantiateRecVar] at Eq
      case box w =>
      constructor
      apply Var.WellScopedRec_instantiateRec (u := u)
      rw [Eq]
      exact v.WS
    · case unbox n _ _ v.WS =>
      cases e <;> simp [instantiateRecVar] at Eq
      case unbox w =>
      constructor
      apply Var.WellScopedRec_instantiateRec (u := u)
      rw [Eq]
      exact v.WS

  @[aesop safe forward]
  lemma WellScoped_implies_WellScopedRec_0 :
    WellScoped e →
    WellScopedRec 0 e
  := by
    intros WS
    induction' WS <;> constructor <;> aesop

  @[aesop safe forward]
  lemma WellScopedRec_weaken :
    m <= n →
    WellScopedRec m e→
    WellScopedRec n e
  := by
    intros leq WS
    induction' WS generalizing n
    · case var m v v.WS =>
      constructor
      apply Var.WellScopedRec_weaken (m := m) leq v.WS
    · case abs m T e T.WS e.WS e.IH =>
      constructor
      · apply Typ.WellScopedRec_weaken (m := m) leq T.WS
      · apply e.IH; linarith
    · case app m f e f.WS e.WS =>
      constructor
        <;> apply Var.WellScopedRec_weaken (m := m) leq
        <;> assumption
    · case tabs m T e T.WS e.WS e.IH =>
      constructor
      · apply Typ.WellScopedRec_weaken (m := m) leq T.WS
      · apply e.IH; linarith
    · case tapp m f T f.WS T.WS =>
      constructor
      · apply Var.WellScopedRec_weaken (m := m) leq f.WS
      · apply Typ.WellScopedRec_weaken (m := m) leq T.WS
    · case let_ m e1 e2 e1.WS e2.WS e1.IH e2.IH =>
      constructor
      · apply e1.IH leq
      · apply e2.IH (n := n + 1); linarith
    · case type m T e _ T.WS e.WS e.IH =>
      constructor
      · apply Typ.WellScopedRec_weaken (m := m) leq T.WS
      · apply e.IH (n := n + 1); linarith
    · case box m v _ v.WS =>
      constructor
      apply Var.WellScopedRec_weaken (m := m) leq v.WS
    · case unbox m v _ v.WS =>
      constructor
      apply Var.WellScopedRec_weaken (m := m) leq v.WS

  instance instWellScopedness : WellScopedness (Exp i) where
    WellScopedRec := WellScopedRec
    WellScoped := WellScoped
    WellScoped_implies_WellScopedRec_0 := WellScoped_implies_WellScopedRec_0
    WellScopedRec_weaken := WellScopedRec_weaken

  @[aesop safe forward]
  lemma substituteVar_fresh :
    x ∉ freeVariablesVar e →
    substituteVar e x u = e
  := by induction e <;> aesop

  @[aesop safe forward]
  lemma instantiateRecVar_WellScopedRec :
    WellScopedRec n e →
    k >= n →
    instantiateRecVar e k u = e
  := by
    intros WS geq
    induction WS generalizing k <;> simp [instantiateRecVar]
    · case var v v.WS =>
      apply Var.instantiateRec_WellScopedRec v.WS geq
    · case abs T e T.WS e.WS e.IH =>
      aesop
    · case app f e f.WS e.WS =>
      apply And.intro
        <;> apply Var.instantiateRec_WellScopedRec
        <;> assumption
    · case tabs T e T.WS e.WS e.IH =>
      apply e.IH (k := k + 1); linarith
    · case tapp f T f.WS T.WS =>
      apply Var.instantiateRec_WellScopedRec <;> assumption
    · case let_ e1 e2 e1.WS e2.WS e1.IH e2.IH =>
      aesop
    · case type T e T.WS e.WS e.IH =>
      aesop
    · case box v v.WS =>
      apply Var.instantiateRec_WellScopedRec v.WS geq
    · case unbox v v.WS =>
      apply Var.instantiateRec_WellScopedRec v.WS geq

  instance : Scoped (Exp i) (.var i) where
    instantiateRec := instantiateRecVar
    substitute := substituteVar
    substitute_fresh := substituteVar_fresh
    instantiateRec_WellScopedRec := instantiateRecVar_WellScopedRec
    WellScopedRec_instantiateRec := WellScopedRec_instantiateRecVar

  @[aesop safe forward]
  lemma substituteTyp_fresh :
    X ∉ freeVariablesTyp e →
    substituteTyp e X U = e
  := by
    intros x.NotIn
    induction e <;> simp [freeVariablesTyp] at x.NotIn <;> simp [substituteTyp]
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

  instance : Scoped (Exp i) (.tvar i) where
    instantiateRec := instantiateRecTyp
    substitute := substituteTyp
    substitute_fresh := substituteTyp_fresh
    WellScopedRec_instantiateRec := WellScopedRec_instantiateRecTyp
    instantiateRec_WellScopedRec := instantiateRecTyp_WellScopedRec
end Exp
