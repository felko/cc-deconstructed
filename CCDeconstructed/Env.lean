import CCDeconstructed.CC
import CCDeconstructed.Var
import CCDeconstructed.Syntax

import Mathlib.Data.Finset.Basic

set_option linter.unusedVariables false

open VarCat Feature

inductive Binding {i : CC} : VarCat i → Type where
  | val : Binding (.var i)
  | sub : Binding (.tvar i)
  | typ [HasFeature i type_bindings] : Binding (.tvar i)

set_option genInjectivity false
@[aesop safe [constructors, cases]]
structure Assoc (i : CC) where
  cat : VarCat i
  name : Atom cat
  binding : Binding cat
  type : Typ i

namespace Assoc
  @[match_pattern]
  def val (x : Atom (.var i)) (T : Typ i) : Assoc i :=
    ⟨_, x, .val, T⟩

  @[match_pattern]
  def sub (X : Atom (.tvar i)) (S : Typ i) : Assoc i :=
    ⟨_, X, .sub, S⟩

  @[match_pattern]
  def typ (X : Atom (.tvar i)) (T : Typ i) : Assoc i :=
    ⟨_, X, .typ, T⟩

  infix:80 " ⦂ " => val
  infix:80 " <: " => sub
  infix:80 " ≔ " => typ

  @[simp] lemma val_name : (x ⦂ T).name = x := rfl
  @[simp] lemma sub_name : (X <: S).name = X := rfl
  @[simp] lemma typ_name : (X ≔ T).name = X := rfl

  @[simp] lemma val_typ : (x ⦂ T).type = T := rfl
  @[simp] lemma sub_typ : (X <: S).type = S := rfl
  @[simp] lemma typ_typ : (X ≔ T).type = T := rfl

  @[simp] lemma val_cat : (x ⦂ T).cat = .var _ := rfl
  @[simp] lemma sub_cat : (X <: S).cat = .tvar _ := rfl
  @[simp] lemma typ_cat : (X ≔ T).cat = .tvar _ := rfl

  def map (f : Typ i → Typ i) : Assoc i → Assoc i
    | ⟨α, x, b, T⟩ => ⟨α, x, b, f T⟩

  @[simp] lemma val_map : map f (x ⦂ T) = (x ⦂ f T) := rfl
  @[simp] lemma sub_map : map f (X <: S) = (X <: f S) := rfl
  @[simp] lemma typ_map : map f (X ≔ T) = (X ≔ f T) := rfl

  @[elab_as_elim,eliminator]
  lemma rec_binding.{u} {i : CC} {motive : Assoc i → Sort u}
    (val : ∀ x T, motive (x ⦂ T))
    (sub : ∀ X S, motive (X <: S))
    (typ : ∀ X T, motive (X ≔ T))
    : ∀ a, motive a
  := by
    intros a
    obtain ⟨α, x, b, T⟩ := a
    cases b
    · case mk.val => apply val
    · case mk.sub => apply sub
    · case mk.typ => apply typ

  def dom (a : Assoc i) {α : VarCat i} : Finset (Atom α) :=
    if h : a.cat = α then
      {h ▸ a.name}
    else
      ∅

  @[simp]
  lemma dom_map {f : Typ i → Typ i} {a : Assoc i} :
    dom (map f a) (α := α) = dom a
  := by simp [dom,map]

  @[simp]
  lemma map_id {a : Assoc i} :
    map id a = a
  := by rfl

  @[simp]
  lemma pseudo_inj :
    (⟨α, x, b, T⟩ : Assoc i) = ⟨α', x', b', T'⟩ ↔
      if h : α = α' then
         x = h ▸ x' ∧
         b = h ▸ b' ∧
         T = T'
      else
        False
  := by
    split
    · case inl Eq.cat =>
      cases Eq.cat
      simp
      apply Iff.intro
      · case mp =>
        intros Eq.assoc
        injection Eq.assoc with _ Eq.name Eq.binding Eq.type
        exact ⟨Eq.name, ⟨Eq.binding, Eq.type⟩⟩
      · case mpr =>
        intros Eqs
        obtain ⟨Eq.name, ⟨Eq.binding, Eq.type⟩⟩ := Eqs
        rw [Eq.name,Eq.binding,Eq.type]
    · case inr Neq.cat =>
      apply Iff.intro _ False.rec
      intros Eq.assoc
      injection Eq.assoc with Eq.cat _ _ _
      exact Neq.cat Eq.cat

  @[simp] lemma val_neq_sub : x ⦂ T  ≠ y <: U := by simp [val,sub]
  @[simp] lemma sub_neq_val : x <: T ≠ y ⦂  U := by simp [val,sub]
  @[simp] lemma val_neq_typ : x ⦂ T  ≠ y ≔  U := by simp [val,typ]
  @[simp] lemma typ_neq_val : x ≔ T  ≠ y ⦂  U := by simp [val,typ]
  @[simp] lemma sub_neq_typ : x <: T ≠ y ≔  U := by simp [sub,typ]
  @[simp] lemma typ_neq_sub : x ≔ T  ≠ y <: U := by simp [sub,typ]

  @[simp] lemma val_eq_val_inj : x ⦂  T = y ⦂  U ↔ x = y ∧ T = U := by simp [val]
  @[simp] lemma sub_eq_sub_inj : x <: T = y <: U ↔ x = y ∧ T = U := by simp [sub]
  @[simp] lemma typ_eq_typ_inj : x ≔  T = y ≔  U ↔ x = y ∧ T = U := by simp [typ]
end Assoc

def Env (i : CC) : Type := List (Assoc i)

namespace Env
  @[match_pattern]
  def nil : Env i := []

  @[match_pattern]
  def cons (Γ : Env i) (a : Assoc i) : Env i :=
    a :: Γ

  infixl:70 " ▷ " => cons

  @[simp]
  lemma cons_inj :
    Γ ▷ a = Δ ▷ b ↔ Γ = Δ ∧ a = b
  := by
    simp [cons]
    rw [List.cons_eq_cons,And.comm]

  def concat (Γ Δ : Env i) : Env i :=
    List.append Δ Γ

  def map (f : Typ i → Typ i) (Γ : Env i) : Env i :=
    List.map (Assoc.map f) Γ

  def Key (i : CC) :=
    Σ (α : VarCat i), Atom α

  def keys : Env i → List (Key i)
    | .nil => .nil
    | Γ ▷ ⟨α, x, _, _⟩ => ⟨α, x⟩ :: keys Γ

  instance instEmptyCollection : EmptyCollection (Env i) where
    emptyCollection := nil

  @[simp]
  instance instMembership : Membership (Assoc i) (Env i) := List.instMembershipList

  @[simp]
  instance instAppend : Append (Env i) where
    append := concat

  @[elab_as_elim, eliminator]
  def rec.{u} {motive : Env i → Sort u}
    (nil : motive ∅)
    (cons : ∀ (Γ : Env i) (a : Assoc i),
            motive Γ →
            motive (Γ ▷ a))
    : (Γ : Env i) → motive Γ
    | .nil => nil
    | Γ ▷ a => cons Γ a (rec nil cons Γ)

  def fold.{u} {α : Type u} (f : α → Assoc i → α) (init : α) (Γ : Env i) : α :=
    List.foldl f init Γ

  @[simp]
  lemma fold_nil.{u} {α : Type u} {f : α → Assoc i → α} {init : α} :
    fold f init (∅ : Env i) = init
  := by rfl

  @[simp]
  lemma fold_cons :
    fold f init (Γ ▷ a) = fold f (f init a) Γ
  := by rfl

  @[simp]
  lemma fold_cons_comm.{u} {α : Type u} {f : α → α → α}
    [isAssoc : IsAssociative α f] [isComm : IsCommutative α f]
    {g : Assoc i → α} (init : α) :
    fold (fun acc a => f acc (g a)) init (Γ ▷ a) = f (fold (fun acc a => f acc (g a)) init Γ) (g a)
  := by
    induction Γ using List.reverseRecOn generalizing a
    · case H0 =>
      simp [fold,cons]
    · case H1 Γ b IH =>
      simp [fold,cons,List.foldl] at *
      rw [IH]
      rw [isAssoc.assoc,isAssoc.assoc]
      congr 1
      rw [isComm.comm]

  def dom (Γ : Env i) {α : VarCat i} : Finset (Atom α) :=
    fold (· ∪ Assoc.dom ·) ∅ Γ

  @[simp]
  lemma nil_concat {Γ : Env i} :
    ∅ ++ Γ = Γ
  := by
    simp [Env,HAppend.hAppend,concat,Append.append]
    rw [List.append_nil]

  @[simp]
  lemma concat_nil {Γ : Env i} :
    Γ ++ ∅ = Γ
  := by rfl

  @[simp]
  lemma concat_singleton {Γ : Env i} :
    Γ ++ ∅ ▷ a = Γ ▷ a
  := by rfl

  @[simp]
  lemma concat_cons {Γ : Env i} :
    Γ ++ Δ ▷ a = (Γ ++ Δ) ▷ a
  := by rfl

  lemma concat_assoc {Γ Θ Δ : Env i} :
    (Γ ++ Θ) ++ Δ = Γ ++ (Θ ++ Δ)
  := by
   simp [Env] at Γ Θ Δ
   simp only [instHAppend,concat,Append.append]
   change Δ ++ (Θ ++ Γ) = (Δ ++ Θ) ++ Γ
   rw [List.append_assoc]

  @[simp]
  lemma cons_neq_nil :
    Γ ▷ a ≠ ∅
  := by
    simp [cons]
    intros Eq
    cases Eq

  @[simp]
  lemma concat_eq_nil {Γ Δ : Env i} :
    Γ ++ Δ = ∅ ↔ Γ = ∅ ∧ Δ = ∅
  := by induction Δ <;> simp

  @[simp]
  lemma map_id {Γ : Env i} :
    map id Γ = Γ
  := by
    simp [map]
    conv in Assoc.map id =>
      ext
      rw [Assoc.map_id]
      rfl
    exact List.map_id Γ

  @[aesop safe]
  lemma mem_map_of_mem {Γ : Env i} {f : Typ i → Typ i} {a : Assoc i} :
    a ∈ Γ →
    Assoc.map f a ∈ map f Γ
  := by
    simp [map]
    intros a.In
    apply List.mem_map_of_mem _ a.In

  @[aesop unsafe]
  lemma mem_map {Γ : Env i} {f : Typ i → Typ i} {b : Assoc i} :
    b ∈ map f Γ ↔ ∃ a ∈ Γ, Assoc.map f a = b
  := by
    simp [map]
    exact List.mem_map

  @[simp]
  lemma map_nil {f : Typ i → Typ i} :
    map f ∅ = ∅
  := by rfl

  @[simp]
  lemma map_cons {f : Typ i → Typ i} {Γ : Env i} {a : Assoc i} :
    map f (Γ ▷ a) = map f Γ ▷ Assoc.map f a
  := by rfl

  @[simp]
  lemma map_concat {f : Typ i → Typ i} {Γ Δ : Env i} :
    map f (Γ ++ Δ) = map f Γ ++ map f Δ
  := by simp [map,HAppend.hAppend,concat,Append.append]

  @[simp]
  lemma dom_map {f : Typ i → Typ i} {Γ : Env i} :
    dom (map f Γ) (α := α) = dom Γ
  := by
    simp [map,dom,fold,List.foldl_map]

  @[simp]
  lemma dom_nil {α : VarCat i} :
    dom (α := α) ∅ = ∅
  := by rfl

  @[simp]
  lemma dom_cons {α : VarCat i} (Γ : Env i) (a : Assoc i) :
    dom (Γ ▷ a) (α := α) = dom Γ ∪ Assoc.dom a
  := by
    simp only [dom]
    apply fold_cons_comm

  @[simp]
  lemma dom_concat {α : VarCat i} (Γ Δ : Env i) :
    dom (Γ ++ Δ) (α := α) = dom Γ ∪ dom Δ
  := by
    induction Δ <;> simp
    case cons Δ a IH =>
    simp [IH]

  @[simp]
  lemma mem_nil {a : Assoc i} :
    a ∉ (∅ : Env i)
  := by
    simp [List.instMembershipList]
    intros mem
    cases mem

  @[simp]
  lemma mem_cons {a : Assoc i} :
    a ∈ Γ ▷ b ↔ a ∈ Γ ∨ a = b
  := by
    simp [cons]
    rw [List.mem_cons]
    rw [Or.comm]

  @[simp]
  lemma mem_cons_head {a : Assoc i} :
    a ∈ Γ ▷ a
  := by
    simp [cons]
    rw [List.mem_cons]
    exact Or.inl rfl

  @[simp]
  lemma mem_concat {a : Assoc i} {Γ Δ : Env i}:
    a ∈ Γ ++ Δ ↔ a ∈ Γ ∨ a ∈ Δ
  := by
    simp [HAppend.hAppend,concat,Append.append]
    rw [List.mem_append]
    rw [Or.comm]

  lemma keys_mem_iff {Γ : Env i} {α : VarCat i} {x : Atom α} :
    ⟨α, x⟩ ∈ keys Γ ↔ ∃ b T, ⟨_, x, b, T⟩ ∈ Γ
  := by
    induction Γ
    · case nil => simp [keys]
    · case cons Γ a IH =>
      obtain ⟨β, y, c, U⟩ := a
      simp [dom_cons,Assoc.dom,keys]
      split
      · case inl Eq.cat =>
        cases Eq.cat
        cases decEq x y
        · case isFalse Neq.name =>
          simp [Neq.name,keys]
          apply Iff.intro
          · case mp =>
            intros Eqs
            cases Eqs
            · case inl Eq.keys =>
              injection Eq.keys with _ Eq.name
              exfalso
              exact (Neq.name Eq.name)
            · case inr x.In =>
              apply IH.mp x.In
          · case mpr =>
            intros x.In
            apply Or.inr
            apply IH.mpr x.In
        · case isTrue Eq.name =>
          cases Eq.name
          simp
          exists c, U
          simp
      · case inr Neq.cat =>
        simp
        apply Iff.intro
        · case mp =>
          intros x.In
          rcases x.In with ⟨Eq.x⟩ | ⟨x.In⟩
          · exfalso
            apply Neq.cat
            injection Eq.x with Eq.cat _
          · apply IH.mp x.In
        · case mpr =>
          intros x.In
          obtain ⟨b, ⟨T, x.In⟩⟩ := x.In
          apply Or.inr
          apply IH.mpr
          exists b, T

  lemma dom_mem_iff {Γ : Env i} {α : VarCat i} {x : Atom α} :
    x ∈ dom Γ (α := α) ↔ ∃ b T, ⟨_, x, b, T⟩ ∈ Γ
  := by
    induction Γ
    · case nil => simp
    · case cons Γ a IH =>
      obtain ⟨β, y, c, U⟩ := a
      simp [dom_cons,Assoc.dom]
      split
      · case inl Eq.cat =>
        cases Eq.cat
        cases decEq x y
        · case isFalse Neq.name =>
          simp [Neq.name]
          exact IH
        · case isTrue Eq.name =>
          cases Eq.name
          simp
          exists c, U
          simp
      · case inr Neq.cat =>
        replace Neq.cat : α ≠ β := Neq.cat ∘ Eq.symm
        simp [Neq.cat]
        exact IH

  lemma dom_keys {Γ : Env i} {α : VarCat i} {x : Atom α} :
    x ∈ dom Γ (α := α) ↔ ⟨_, x⟩ ∈ keys Γ
  := by
    induction Γ
    · case nil => simp [keys_mem_iff]
    · case cons Γ a IH =>
      obtain ⟨β, y, c, U⟩ := a
      simp [dom_cons,Assoc.dom]
      split
      · case inl Eq.cat =>
        cases Eq.cat
        cases decEq x y
        · case isFalse Neq.name =>
          simp [keys_mem_iff,Neq.name] at *
          exact IH
        · case isTrue Eq.name =>
          cases Eq.name
          simp [keys_mem_iff]
          exists c, U
          simp
      · case inr Neq.cat =>
        replace Neq.cat : α ≠ β := Neq.cat ∘ Eq.symm
        simp [keys_mem_iff,Neq.cat] at *
        exact IH

  @[simp]
  lemma keys_nil :
    keys (∅ : Env i) = []
  := by rfl

  @[simp]
  lemma keys_concat {Γ Δ : Env i} :
    keys (Γ ++ Δ) = keys Δ ++ keys Γ
  := by
    induction Δ <;> simp
    case cons Δ a IH =>
    cases a <;> simp [keys,IH]

  def Forall : (Assoc i → Prop) → Env i → Prop :=
    List.Forall

  namespace Forall
    @[simp] lemma Forall_nil : Forall P ∅ = True := by rfl
    @[simp] lemma Forall_cons : Forall P (Γ ▷ a) ↔ Forall P Γ ∧ P a := by simp [cons,Forall,And.comm]

    def imp (h : ∀ (a : Assoc i), P a → Q a) : Forall P Γ → Forall Q Γ :=
      List.Forall.imp h

    def forall_iff_forall_mem {Γ : Env i} : Env.Forall P Γ ↔ ∀ a ∈ Γ, P a :=
      List.forall_iff_forall_mem

    def mem {Γ : Env i} (h : Forall P Γ) {a : Assoc i} (mem : a ∈ Γ) : P a :=
      forall_iff_forall_mem.mp h _ mem
  end Forall

  @[aesop norm]
  def Nodup (Γ : Env i) :=
    List.Nodup (keys Γ)

  namespace Nodup
    @[simp]
    lemma nil :
      Nodup (∅ : Env i)
    := by simp [Nodup,keys]

    @[simp]
    lemma cons {Γ : Env i} {a : Assoc i} :
      Nodup Γ ->
      a.name ∉ dom Γ →
      Nodup (Γ ▷ a)
    := by
      intros Γ.Nodup a.NotIn
      simp [Nodup,cons,keys]
      apply And.intro _ Γ.Nodup
      simp [keys_mem_iff]
      intros b T
      obtain NotIn := dom_mem_iff.not.mp a.NotIn
      intros a.In
      apply NotIn ⟨b, ⟨T, a.In⟩⟩

    @[aesop unsafe]
    lemma left_of_concat {Γ Δ : Env i} :
      Nodup (Γ ++ Δ) ->
      Nodup Γ
    := by
      intros nodup
      simp [Nodup,List.Nodup] at *
      exact (List.pairwise_append.mp nodup).2.1

    @[elab_as_elim, eliminator]
    lemma rec.{u} {motive : (Γ : Env i) → Nodup Γ → Sort u}
      (nil : motive ∅ Nodup.nil)
      (cons : ∀ {Γ : Env i} {a : Assoc i} {nodup : Nodup Γ}
                (NotIn : a.name ∉ dom Γ)
                (IH : motive Γ nodup),
                motive (Γ ▷ a) (Nodup.cons nodup NotIn))
      : ∀ {Γ}, (nodup : Nodup Γ) → motive Γ nodup
    := by
      intros Γ nodup
      induction Γ
      · case nil =>
        exact nil
      · case cons Γ a IH =>
        simp [Nodup,keys] at nodup
        obtain ⟨NotIn, nodup⟩ := nodup
        rw [<- dom_keys] at NotIn
        exact cons NotIn (IH nodup)

    @[simp]
    lemma unique {Γ : Env i} {α : VarCat i} {x : Atom α} {b₁ b₂ : Binding α} {T₁ T₂ : Typ i} :
      Nodup Γ →
      (⟨α, x, b₁, T₁⟩ : Assoc i) ∈ Γ →
      (⟨α, x, b₂, T₂⟩ : Assoc i) ∈ Γ →
      b₁ = b₂ ∧ T₁ = T₂
    := by
      intros Nodup Mem₁ Mem₂
      induction Nodup generalizing α x b₁ b₂ T₁ T₂ <;> simp at *
      case cons Γ c Nodup c.NotIn IH =>
      cases Mem₁ <;> cases Mem₂
      · case inl.inl Mem₁ Mem₂ =>
        exact IH Mem₁ Mem₂
      · case inl.inr Mem₁ Eq₂ =>
        cases Eq₂
        exfalso
        apply c.NotIn
        apply dom_mem_iff.mpr
        exists b₁, T₁
      · case inr.inl Eq₁ Mem₂ =>
        cases Eq₁
        exfalso
        apply c.NotIn
        apply dom_mem_iff.mpr
        exists b₂, T₂
      · case inr.inr Eq₁ Eq₂ =>
        cases Eq₁
        cases Eq₂
        simp

    lemma mid {Γ : Env i} {α : VarCat i} {x : Atom α} {b : Binding α} {T : Typ i} {Δ : Env i} :
      Nodup (Γ ▷ ⟨α, x, b, T⟩ ++ Δ) →
      x ∉ dom Γ ∧ x ∉ dom Δ
    := by
      intros nodup
      induction Δ
      · case nil =>
        cases nodup
        simp
        assumption
      · case cons Δ a IH =>
        simp
        rw [concat_cons] at nodup
        cases nodup
        rename_i nodup NotIn IH; clear IH
        obtain ⟨x.NotInΓ, x.NotInΔ⟩ := IH nodup
        simp [x.NotInΓ,x.NotInΔ]
        simp at NotIn
        cases a
        all_goals {
          rename_i y U
          simp [Assoc.dom] at *
          split <;> aesop
        }
  end Nodup
end Env

attribute [irreducible] Env

@[simp] instance : EmptyCollection (Env i) := Env.instEmptyCollection
@[simp] instance : Membership (Assoc i) (Env i) := Env.instMembership
@[simp] instance : Append (Env i) := Env.instAppend
