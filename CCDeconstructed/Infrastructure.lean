import CCDeconstructed.Syntax
import CCDeconstructed.Classes
import CCDeconstructed.Tactics

open Scoped FreeVariables VarCat

attribute [simp,aesop norm unfold] Coe.coe

namespace Var
  instance : Coe (Atom α) (Var α) where
    coe := Var.free

  instance : Coe (Index α) (Var α) where
    coe := Var.bound

  @[aesop norm]
  def fv : Var α -> Finset (Atom α)
      | .free x => {x}
      | .bound _ => ∅
      | .cap => ∅

  @[aesop norm]
  def bv : Var α -> Finset (Index α)
    | .free _ => ∅
    | .bound i => {i}
    | .cap => ∅

  @[simp,aesop norm]
  def subst [Coe (Var α) β] (v : Var α) (x : Var α) (u : β) : β :=
    if v = x then u else v

  @[aesop norm]
  def substitute {i} {α : VarCat i} (v : Var α) (x : Atom α) (u : Var α) : Var α :=
    @subst i α (Var α) ⟨id⟩ v (.free x) u

  @[aesop norm]
  def instantiateRec {i} {α : VarCat i} (v : Var α) (k : Index α) (u : Var α) : Var α :=
    @subst i α (Var α) ⟨id⟩ v (.bound k) u

  instance instFreeVariables : FreeVariables (Var α) α where
    fv := fv

  @[aesop norm]
  def WellScopedRec {i : CC} {α : VarCat i} (n : Nat) : Var α -> Prop
    | .bound k => k < n
    | _ => True

  @[aesop norm]
  def WellScoped {i : CC} {α : VarCat i} : Var α -> Prop
    | .bound _ => False
    | _ => True

  @[aesop safe forward]
  lemma WellScoped_implies_WellScopedRec_0 :
    WellScoped t ->
    WellScopedRec 0 t
  := by simp [WellScoped,WellScopedRec]

  @[aesop safe forward]
  lemma WellScopedRec_weaken :
    m <= n ->
    WellScopedRec m v ->
    WellScopedRec n v
  := by
    simp [WellScopedRec]
    intros
    cases v <;> simp [Index] at *
    linarith

  instance instWellScoping : WellScoping (Var α) where
    WellScopedRec := WellScopedRec
    WellScoped := WellScoped
    WellScoped_implies_WellScopedRec_0 := WellScoped_implies_WellScopedRec_0
    WellScopedRec_weaken := WellScopedRec_weaken

  @[aesop safe forward]
  lemma substitute_fresh :
    x ∉ fv v ->
    substitute v x u = v
  := by simp [fv,substitute]; aesop

  @[aesop safe forward]
  lemma WellScopedRec_instantiateRec :
    WellScopedRec n (instantiateRec v n u) ->
    WellScopedRec (n + 1) v
  := by
    simp [WellScopedRec]
    intros WS
    cases v <;> simp [instantiateRec] at WS <;> simp
    case bound k =>
    cases (decEq k n) <;> rename_i H <;> simp [H,Index] at *
    linarith

  @[aesop safe forward]
  lemma instantiateRec_WellScopedRec :
    WellScopedRec n v ->
    k >= n ->
    instantiateRec v k u = v
  := by
    simp [instantiateRec,WellScopedRec]
    intros WS leq v.Bound
    cases v <;> simp [Index] at *
    case bound k => exfalso; linarith

  instance instScoped : Scoped (Var (.var i)) (.var i) where
    instantiateRec := instantiateRec
    substitute := substitute
    substitute_fresh := substitute_fresh
    WellScopedRec_instantiateRec := WellScopedRec_instantiateRec
    instantiateRec_WellScopedRec := instantiateRec_WellScopedRec
end Var

namespace Cap
  @[aesop norm]
  def fv (C : Cap i) : Finset (Atom (var i)) :=
    C.fold (· ∪ ·) ∅ Var.fv

  lemma mem_free_iff_mem_fv :
    .free x ∈ C <-> x ∈ fv C
  := by
    induction' C using Finset.induction <;> aesop

  @[aesop safe apply]
  lemma mem_free_implies_mem_fv :
    .free x ∈ C -> x ∈ fv C
  := Iff.mp mem_free_iff_mem_fv

  lemma mem_fv_implies_mem_free :
    x ∈ fv C -> .free x ∈ C
  := Iff.mpr mem_free_iff_mem_fv

  @[aesop norm]
  def bv (C : Cap i) : Finset (Index (var i)) :=
    C.fold (· ∪ ·) ∅ Var.bv

  lemma mem_bound_iff_mem_bv :
    .bound k ∈ C <-> k ∈ bv C
  := by
    induction' C using Finset.induction <;> aesop

  @[aesop safe apply]
  lemma mem_bound_implies_mem_bv :
    .bound k ∈ C -> k ∈ bv C
  := Iff.mp mem_bound_iff_mem_bv

  lemma mem_bv_implies_mem_bound :
    k ∈ bv C -> .bound k ∈ C
  := Iff.mpr mem_bound_iff_mem_bv

  instance : FreeVariables (Cap i) (var i) where
    fv := fv

  @[aesop norm 10]
  def instantiateRec (C : Cap i) (k : Index (var i)) (u : Var (var i)) :=
    if .bound k ∈ C then
      C \ {.bound k} ∪ {u}
    else
      C

  @[aesop norm 10]
  def substitute (C : Cap i) (x : Atom (var i)) (u : Var (var i)) :=
    if .free x ∈ C then
      C \ {.free x} ∪ {u}
    else
      C

  @[aesop norm 5]
  def WellScopedRec (n : Nat) (C : Cap i) :=
    ∀ v ∈ C, Var.WellScopedRec n v

  @[aesop norm 5]
  def WellScoped (C : Cap i) :=
    ∀ v ∈ C, Var.WellScoped v

  @[aesop safe forward]
  lemma WellScoped_implies_WellScopedRec_0 :
    WellScoped C ->
    WellScopedRec 0 C
  := by aesop

  @[simp,aesop safe forward]
  lemma WellScopedRec_weaken :
    m <= n ->
    WellScopedRec m C ->
    WellScopedRec n C
  := by
    intros leq C.WS v v.In
    apply Var.WellScopedRec_weaken <;> aesop

  instance instWellScoping : WellScoping (Cap i) where
    WellScopedRec := WellScopedRec
    WellScoped := WellScoped
    WellScoped_implies_WellScopedRec_0 := WellScoped_implies_WellScopedRec_0
    WellScopedRec_weaken := WellScopedRec_weaken

  lemma substitute_fresh :
    x ∉ fv C ->
    substitute C x u = C
  := by
    simp [substitute]
    intros x.NotIn x.In
    exfalso; apply x.NotIn
    apply mem_free_implies_mem_fv x.In

  @[simp]
  lemma WellScopedRec_instantiateRec :
    WellScopedRec n (instantiateRec C n u) ->
    WellScopedRec (n + 1) C
  := by
    intros C.WS v v.WS
    apply Var.WellScopedRec_instantiateRec (u := u)
    apply C.WS
    simp only [instantiateRec]
    aesop

  @[simp]
  lemma instantiateRec_WellScopedRec :
    WellScopedRec n C ->
    k >= n ->
    instantiateRec C k u = C
  := by aesop

  @[simp]
  instance instScoped : Scoped (Cap i) (var i) where
    instantiateRec := instantiateRec
    substitute := substitute
    substitute_fresh := substitute_fresh
    WellScopedRec_instantiateRec := WellScopedRec_instantiateRec
    instantiateRec_WellScopedRec := instantiateRec_WellScopedRec

  instance instEmptyCollection : EmptyCollection (Cap i) := inferInstance
  instance instSingleton : Singleton (Var (.var i)) (Cap i) := inferInstance
  instance instMembership : Membership (Var (.var i)) (Cap i) := inferInstance
end Cap

instance : EmptyCollection (Cap i) := Cap.instEmptyCollection
instance : Singleton (Var (.var i)) (Cap i) := Cap.instSingleton
instance : Membership (Var (.var i)) (Cap i) := Cap.instMembership

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
  inductive WellScopedRec {i : CC} : Nat -> Typ i -> Prop :=
    | top : WellScopedRec n .top
    | var : Var.WellScopedRec n V -> WellScopedRec n (.var V)
    | arr :
        WellScopedRec n A ->
        WellScopedRec (n + 1) B ->
        WellScopedRec n (.arr A B)
    | all :
        WellScopedRec n A ->
        WellScopedRec (n + 1) B ->
        WellScopedRec n (.all k A B)
    | box [HasFeature i .box_type] :
        WellScopedRec n T ->
        WellScopedRec n (.box T)
    | cap :
       WellScopedRec n S ->
       Cap.WellScopedRec n C ->
       WellScopedRec n (.cap S C)

  @[aesop unsafe [constructors 50%]]
  inductive WellScoped {i : CC} : Typ i -> Prop :=
    | top : WellScoped .top
    | var : WellScoping.WellScoped V -> WellScoped (.var V)
    | arr (L : Finset (Atom (.var i))) :
        WellScoped T ->
        (∀ (x : Atom (.var i)), x ∉ L -> WellScoped (U.instantiateRecVar 0 (.free x))) ->
        WellScoped (.arr T U)
    | all (L : Finset (Atom (tvar i))) :
        WellScoped S ->
        (∀ (X : Atom (.tvar i)), X ∉ L -> WellScoped (U.instantiateRecTyp 0 (Typ.var X))) ->
        WellScoped (.all k S U)
    | box [HasFeature i box_type] :
        WellScoped T ->
        WellScoped (.box T)
    | cap [HasFeature i .box_type] :
       WellScoped S ->
       WellScoping.WellScoped C ->
       WellScoped (.cap S C)

  @[aesop safe forward]
  lemma WellScopedRec_instantiateRecTyp :
    WellScopedRec n (instantiateRecTyp T n U) ->
    WellScopedRec (n + 1) T
  := by
    intros T.WS
    generalize Eq : instantiateRecTyp T n U = T'
    rw [Eq] at T.WS
    induction' T.WS generalizing T U
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
    WellScopedRec n (instantiateRecVar T n u) ->
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

  @[aesop safe forward]
  lemma WellScoped_implies_WellScopedRec_0 :
    WellScoped T ->
    WellScopedRec 0 T
  := by
    intros WS
    induction WS <;> constructor <;> aesop
    · pick_fresh x ∉ L
      apply WellScopedRec_instantiateRecVar (u := .free x)
      aesop
    · pick_fresh X ∉ L
      apply WellScopedRec_instantiateRecTyp (U := .var (.free X))
      aesop

  @[aesop safe forward]
  lemma WellScopedRec_weaken :
    m <= n ->
    WellScopedRec m T ->
    WellScopedRec n T
  := by
    intros leq WS
    induction' WS generalizing n <;> constructor <;> aesop
    linarith

  instance instWellScoping : WellScoping (Typ i) where
    WellScopedRec := WellScopedRec
    WellScoped := WellScoped
    WellScoped_implies_WellScopedRec_0 := WellScoped_implies_WellScopedRec_0
    WellScopedRec_weaken := WellScopedRec_weaken

  @[aesop safe forward]
  lemma substituteTyp_fresh :
    X ∉ freeVariablesTyp T ->
    substituteTyp T X U = T
  := by induction T <;> aesop

  @[aesop safe forward]
  lemma instantiateRecTyp_WellScopedRec :
    WellScopedRec n T ->
    K >= n ->
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
    x ∉ freeVariablesVar T ->
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
    WellScopedRec n T ->
    k >= n ->
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
    | .let e1 e2 => e1.freeVariablesVar ∪ e2.freeVariablesVar
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
    | .let e1 e2 => e1.freeVariablesTyp ∪ e2.freeVariablesTyp
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
    | .let e1 e2 => .let (e1.instantiateRecVar k u) (e2.instantiateRecVar (k + 1) u)
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
    | .let e1 e2 => .let (e1.substituteVar x u) (e2.substituteVar x u)
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
    | .let e1 e2 => .let (e1.instantiateRecTyp K U) (e2.instantiateRecTyp (K + 1) U)
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
    | .let e1 e2 => .let (e1.substituteTyp X U) (e2.substituteTyp X U)
    | @Exp.type _ _ T e => .type (T.substituteTyp X U) (e.substituteTyp X U)
    | @Exp.box _ _ x => .box x
    | @Exp.unbox _ _ x => .unbox x

  @[aesop unsafe constructors 50%]
  inductive WellScopedRec {i : CC} : Nat -> Exp i -> Prop :=
    | var :
        Var.WellScopedRec n v ->
        WellScopedRec n (.var v)
    | abs :
        Typ.WellScopedRec n T ->
        WellScopedRec (n + 1) e ->
        WellScopedRec n (.abs T e)
    | app :
        Var.WellScopedRec n f ->
        Var.WellScopedRec n e ->
        WellScopedRec n (.app f e)
    | tabs :
        Typ.WellScopedRec n T ->
        WellScopedRec (n + 1) e ->
        WellScopedRec n (.tabs T e)
    | tapp :
        Var.WellScopedRec n f ->
        Typ.WellScopedRec n T ->
        WellScopedRec n (.tapp f T)
    | let :
        WellScopedRec n e1 ->
        WellScopedRec (n + 1) e2 ->
        WellScopedRec n (.let e1 e2)

  -- /-
  inductive Scope {i} {α : VarCat i} (F : Var α -> Prop) : Prop where
    | intro (L : Finset (Atom α)) : ∀ x ∉ L, F (.free x) -> Scope F

  section
    open Lean.TSyntax.Compat
    macro "⦃" x:ident " | " b:term "⦄" : term => `(Scope (fun $x => $b))
  end
  -- -/

  /-
  def Scope {i} (β : VarCat i) [s : Scoped α β] [Coe (Var β) (VarCat.type β)] (f : α -> Prop) (e : α) : Prop :=
    ∃ L : Finset (Atom β), ∀ x ∉ L, f (@Scoped.instantiate α i β s e (@Var.free i β x))
  -/

  @[aesop unsafe constructors 50%]
  inductive WellScoped {i : CC} : Exp i -> Prop :=
    | var :
        Var.WellScoped v ->
        WellScoped (.var v)
    | abs :
        Typ.WellScoped T ->
        ⦃ x | WellScoped (e.instantiateRecVar 0 x) ⦄ ->
        WellScoped (.abs T e)
    | app :
        Var.WellScoped f ->
        Var.WellScoped e ->
        WellScoped (.app f e)
    | tabs :
        Typ.WellScoped T ->
        Scope (.tvar i) WellScoped e ->
        WellScoped (.tabs T e)
    | tapp :
        Var.WellScoped f ->
        Typ.WellScoped T ->
        WellScoped (.tapp f T)
    | let (L : Finset (Atom (.var i))) :
        WellScoped e1 ->
        Scope (.var i) WellScoped e2 ->
        WellScoped (.let e1 e2)

  instance : WellScoping (Exp i) where
    WellScoped := WellScoped

  instance : Scoped (Exp i) (.var i) where
    instantiateRec := instantiateRecVar
    substitute := substituteVar

  instance : Scoped (Exp i) (.tvar i) where
    instantiateRec := instantiateRecTyp
    substitute := substituteTyp
end Exp


/-
theorem Var.substWellScopedIdempotent [Coe (Var α) β] : ∀ (v : Var α) (t : β) (k : Index α),
  WellScoped v ->
  v.subst k t = v
:= by
  intros v w k v.WS
  cases v.WS
  case free x =>
  simp [instantiateRec,subst]

theorem Typ.instantiateRecWellScoped : ∀ (t u : Typ i) (k : Nat),
  WellScoped t ->
  t.instantiateRec k u = t
:= by
  introv WS
  revert k
  induction WS <;> intro k <;> simp [Scoped.instantiate, Typ.instantiateRec] at *
  · case var v v.WS =>
    apply Var.substWellScoped
    exact v.WS
  · case arr A B A.WS B.WS A.IH B.IH =>
    apply And.intro
    · apply (A.IH k)
    · apply (B.IH k)
  · case all A B L A.WS B.WS A.IH B.IH =>
    apply And.intro
    · apply (A.IH k)
    · pick_fresh Y ∉ L
      have IB.WS : WellScoped (B.instantiateRec 0 Y) := by
        apply (B.WS Y YFr)
      rw [B.IH]


    cases A.WS
    simp [Var.instantiateRec, Coe.coe]
  · rename_i A.IH B.IH
    apply And.intro
    · exact (A.IH k)
    · exact (B.IH k)
  · rename_i A x B L A.WS B.WS A.IH B.IH
    apply And.intro
    · exact (A.IH k)
    · pick_fresh Y : Typ
      specialize B.IH Y

      sorry
  · sorry
  · sorry
-/
