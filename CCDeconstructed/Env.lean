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
  @[simp]
  def val (x : Atom (.var i)) (T : Typ i) : Assoc i :=
    ⟨_, x, .val, T⟩

  def sub (X : Atom (.tvar i)) (S : Typ i) : Assoc i :=
    ⟨_, X, .sub, S⟩

  def typ (X : Atom (.tvar i)) (T : Typ i) : Assoc i :=
    ⟨_, X, .typ, T⟩

  infix:80 " ⦂ " => val
  infix:80 " <: " => sub
  infix:80 " ≔ " => typ

  def dom (a : Assoc i) {α : VarCat i} : Finset (Atom α) :=
    if h : a.cat = α then
      {h ▸ a.name}
    else
      ∅

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
end Assoc

def Env (i : CC) : Type := List (Assoc i)

namespace Env
  @[match_pattern]
  def nil : Env i := []

  @[match_pattern]
  def cons (Γ : Env i) (a : Assoc i) : Env i :=
    a :: Γ

  infixl:70 " ▷ " => cons

  def concat (Γ Δ : Env i) : Env i :=
    List.append Δ Γ

  def Key (i : CC) :=
    Σ (α : VarCat i), Atom α

  def keys : Env i → List (Key i)
    | .nil => .nil
    | Γ ▷ ⟨α, x, _, _⟩ => ⟨α, x⟩ :: keys Γ

  def dom (Γ : Env i) {α : VarCat i} : Finset (Atom α) :=
    List.foldl (· ∪ Assoc.dom ·) ∅ Γ

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


  @[simp]
  lemma dom_nil {α : VarCat i} :
    dom (α := α) ∅ = ∅
  := by rfl

  @[simp]
  lemma dom_cons {α : VarCat i} (Γ : Env i) (a : Assoc i) :
    dom (Γ ▷ a) (α := α) = dom Γ ∪ Assoc.dom a
  := by
    induction Γ using List.reverseRecOn
    · case H0 =>
      simp [dom,cons,List.foldl]
    · case H1 Γ b IH =>
      simp [dom,cons] at *
      rw [IH]
      simp
      congr 1
      apply Finset.union_comm

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
  lemma mem_concat {a : Assoc i} {Γ Δ : Env i}:
    a ∈ Γ ++ Δ ↔ a ∈ Γ ∨ a ∈ Δ
  := by
    simp [HAppend.hAppend,concat,Append.append]
    rw [List.mem_append]
    rw [Or.comm]

  @[simp]
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

  @[simp]
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

  @[simp]
  lemma dom_keys {Γ : Env i} {α : VarCat i} {x : Atom α} :
    x ∈ dom Γ (α := α) ↔ ⟨_, x⟩ ∈ keys Γ
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
        · case isTrue Eq.name =>
          cases Eq.name
          simp
          exists c, U
          simp
      · case inr Neq.cat =>
        replace Neq.cat : α ≠ β := Neq.cat ∘ Eq.symm
        simp [Neq.cat]

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
      intros b T
      obtain NotIn := dom_mem_iff.not.mp a.NotIn
      intros a.In
      apply NotIn ⟨b, ⟨T, a.In⟩⟩
  end Nodup
end Env

/-
namespace Atom
  @[aesop safe [constructors, cases]]
  inductive HasName {α : VarCat i} : Atom α → {β : VarCat i} → Atom β → Prop where
    | hasName : HasName x x

  @[simp]
  lemma HasName.to_eq {α : VarCat i} {x y : Atom α} :
    x.HasName y ↔ x = y
  := by aesop

  @[simp]
  lemma HasName.comm {α β : VarCat i} {x : Atom α} {y : Atom β} :
    x.HasName y ↔ y.HasName x
  := by aesop

  @[aesop unsafe 20%]
  instance decidableHasName {α β : VarCat i} (x : Atom α) (y : Atom β) : Decidable (x.HasName y) := by
    cases decEq α β
    · case isFalse Neq.cat =>
      apply isFalse
      intros hasName
      cases hasName
      exact Neq.cat rfl
    · case isTrue Eq.cat =>
      cases Eq.cat
      cases decEq x y
      · case isFalse Neq.name =>
        apply isFalse
        intros hasName
        cases hasName
        exact Neq.name rfl
      · case isTrue Eq.name =>
        apply isTrue
        cases Eq.name
        constructor
end Atom

@[aesop [unsafe constructors 80%, unsafe cases 10%]]
inductive Binding : VarCat i → Type :=
  | val : Typ i → Binding (var i)
  | sub : Typ i → Binding (tvar i)
  | typ [HasFeature i type_bindings] : Typ i → Binding (tvar i)
  deriving DecidableEq

set_option genInjectivity false
@[aesop safe [constructors, cases]]
structure Binder (i : CC) where
  cat : VarCat i
  name : Atom cat
  deriving DecidableEq

namespace Binder
  @[simp]
  def dom {α : VarCat i} (b : Binder i) : Finset (Atom α) :=
    if h : b.cat = α then
      {h ▸ b.name}
    else
      ∅

  @[simp]
  lemma eq_rect :
    ({ cat := α, name := x } : Binder i) = { cat := β, name := y } ↔ if h : α = β then h ▸ x = y else False
  := by
    apply Iff.intro
    · case mp =>
      intros Eq
      injection Eq with Eq.cat Eq.name
      aesop
    · case mpr =>
      aesop

  @[aesop safe [constructors, cases]]
  inductive HasName : Binder i → {α : VarCat i} → Atom α → Prop where
    | hasName : HasName ⟨α, x⟩ x

  @[simp]
  lemma HasName.to_eq {v : Binder i} {x : Atom v.cat} :
    v.HasName x ↔ v.name = x
  := by aesop

  @[aesop unsafe 20%]
  lemma HasName.in_dom {α : VarCat i} {v : Binder i} {x : Atom α} :
    v.HasName x ↔ x ∈ Binder.dom v
  := by
    simp only [Binder.dom]
    cases α <;> cases v <;> aesop

  @[simp]
  lemma HasName.name {v : Binder i} {x : Atom α} :
    v.HasName x ↔ v.name.HasName x
  := by aesop

  @[simp]
  lemma HasName.comm {α : VarCat i} {v : Binder i} {x : Atom α} :
    v.HasName x ↔ x.HasName v.name
  := by aesop

  @[aesop safe]
  instance decidableHasName (v : Binder i) {α : VarCat i} (x : Atom α) : Decidable (v.HasName x) := by
    cases Atom.decidableHasName v.name x
    · case isFalse hasn'tName =>
      apply isFalse
      intros hasName
      cases hasName
      apply hasn'tName
      constructor
    · case isTrue hasName =>
      apply isTrue
      cases hasName
      constructor
end Binder

@[aesop unsafe [constructors 10%, cases 40%]]
inductive Assoc (i : CC) : Type where
  | val : Atom (var i) → Typ i → Assoc i
  | sub : Atom (tvar i) → Typ i → Assoc i
  | typ [HasFeature i type_bindings] : Atom (tvar i) → Typ i → Assoc i
  deriving DecidableEq

namespace Assoc
  infix:80 " ⦂ " => Assoc.val
  infix:80 " <: " => Assoc.sub
  infix:80 " ≔ " => Assoc.typ

  @[aesop norm]
  def type : Assoc i → Typ i
    | .val _ T => T
    | .sub _ S => S
    | @Assoc.typ _ _ _ T => T

  @[aesop norm]
  def binder : Assoc i → Binder i
    | .val x _ => ⟨.var _, x⟩
    | .sub X _ => ⟨.tvar _, X⟩
    | @Assoc.typ _ _ X _ => ⟨.tvar _, X⟩

  @[aesop norm]
  def name (a : Assoc i) : Atom a.binder.cat :=
    a.binder.name

  @[simp] lemma name_val : (x ⦂  T).name = x := rfl
  @[simp] lemma name_sub : (X <: S).name = X := rfl
  @[simp] lemma name_typ : (X ≔  T).name = X := rfl

  @[aesop norm]
  def cat (a : Assoc i) : VarCat i :=
    a.binder.cat

  @[simp] lemma cat_val {x : Atom (var i)}  : (x ⦂  T).cat = var i := rfl
  @[simp] lemma cat_sub {X : Atom (tvar i)} : (X <: S).cat = tvar i := rfl
  @[simp] lemma cat_typ {X : Atom (tvar i)} : (X ≔  T).cat = tvar i := rfl

  @[aesop norm]
  def dom {α : VarCat i} (a : Assoc i) : Finset (Atom α) :=
    a.binder.dom

  @[simp] lemma dom_var_val  {x : Atom (var i)}  : (x ⦂  T).dom = {x} := rfl
  @[simp] lemma dom_tvar_sub {X : Atom (tvar i)} : (X <: S).dom = {X} := rfl
  @[simp] lemma dom_tvar_typ {X : Atom (tvar i)} : (X ≔  T).dom = {X} := rfl

  @[simp] lemma dom_tvar_val {x : Atom (var i)}  : (x ⦂  T).dom (α := tvar i) = ∅ := rfl
  @[simp] lemma dom_var_sub  {X : Atom (tvar i)} : (X <: S).dom (α := var i) = ∅ := rfl
  @[simp] lemma dom_var_typ  {X : Atom (tvar i)} : (X ≔  T).dom (α := var i) = ∅ := rfl

  @[simp]
  lemma val_inj : (x ⦂  T) = (x' ⦂  T') ↔ x = x' ∧ T = T'
  := by
    apply Iff.intro
    · case mp =>
      intros eq
      injection eq with eq.name eq.type
      apply And.intro eq.name eq.type
    · case mpr => aesop

  @[simp]
  lemma sub_inj : (X <: S) = (X' <: S') ↔ X = X' ∧ S = S'
  := by
    apply Iff.intro
    · case mp =>
      intros eq
      injection eq with eq.name eq.type
      apply And.intro eq.name eq.type
    · case mpr => aesop

  @[simp]
  lemma typ_inj : (X ≔  T) = (X' ≔  T') ↔ X = X' ∧ T = T'
  := by
    apply Iff.intro
    · case mp =>
      intros eq
      injection eq with eq.name eq.type
      apply And.intro eq.name eq.type
    · case mpr => aesop

  @[simp]
  def fromSigma (p : (v : Binder i) × Binding v.cat) : Assoc i :=
    match p with
    | ⟨⟨_, x⟩, .val T⟩ => .val x T
    | ⟨⟨_, X⟩, .sub S⟩ => .sub X S
    | ⟨⟨_, X⟩, @Binding.typ _ _ T⟩ => .typ X T

  @[simp]
  def toSigma : Assoc i → (v : Binder i) × Binding v.cat
    | .val x T => ⟨⟨_, x⟩, .val T⟩
    | .sub X S => ⟨⟨_, X⟩, .sub S⟩
    | @Assoc.typ _ _ X T => ⟨⟨_, X⟩, .typ T⟩

  @[simp]
  def fromSigma_toSigma {a : Assoc i} :
    fromSigma (toSigma a) = a
  := by cases a <;> simp

  @[simp]
  def toSigma_fromSigma {B : (v : Binder i) × Binding v.cat} :
    toSigma (fromSigma B) = B
  := by
    obtain ⟨⟨α, x⟩, b⟩ := B
    simp at b
    cases b <;> simp

  @[simp]
  def isoSigma :
    Assoc i ≃ ((v : Binder i) × Binding v.cat)
  := by
    apply Equiv.mk toSigma fromSigma
    · case left_inv =>
      apply fromSigma_toSigma
    · case right_inv =>
      apply toSigma_fromSigma

  @[simp]
  lemma binder_fromSigma_eq_fst :
    binder (fromSigma B) = B.fst
  := by
    obtain ⟨v, b⟩ := B
    cases v; cases b <;> simp [fromSigma,binder]

  @[simp]
  lemma dom_fromSigma_def {α β : VarCat i} {x : Atom β} {b : Binding β} :
    dom (fromSigma ⟨⟨β, x⟩, b⟩) (α := α) =
      if h : α = β then
        {h ▸ x}
      else ∅
  := by
    simp only [dom,Binder.dom]
    rw [binder_fromSigma_eq_fst]
    split
    · case inl Eq.cat =>
      cases Eq.cat
      simp
    · case inr Neq.cat =>
      replace Neq.cat : α ≠ β := Neq.cat ∘ Eq.symm
      simp [Neq.cat]

  @[simp]
  lemma dom_fromSigma {α : VarCat i} {x : Atom α} {b : Binding α} :
    dom (fromSigma ⟨⟨α, x⟩, b⟩) (α := α) = {x}
  := by
    simp only [dom,Binder.dom]
    rw [binder_fromSigma_eq_fst]
    split
    · case inl Eq.cat =>
      cases Eq.cat
      simp
    · case inr Neq.cat =>
      simp at Neq.cat

  @[simp]
  lemma fromSigma_inj :
    fromSigma p1 = fromSigma p2 →
    p1 = p2
  := by
    intros eq
    cases p1; rename_i x b1; cases p2; rename_i y b2
    cases x; rename_i c x; cases y; rename_i d y
    cases b1 <;> cases b2 <;> rename_i T U <;> cases eq <;> rfl

  @[aesop [safe constructors, unsafe cases 70%]]
  inductive HasName : Assoc i → {α : VarCat i} → Atom α → Prop where
    | val x T : HasName (x ⦂  T) x
    | sub X S : HasName (X <: S) X
    | typ X T : HasName (X ≔  T) X

  @[simp]
  lemma HasName.to_eq {a : Assoc i} {x : Atom a.cat} :
    a.HasName x ↔ a.name = x
  := by aesop

  @[aesop unsafe 20%]
  lemma HasName.in_dom {α : VarCat i} {a : Assoc i} {x : Atom α} :
    a.HasName x ↔ x ∈ Assoc.dom a
  := by
    simp only [Assoc.dom,Assoc.binder]
    cases α <;> cases a <;> aesop

  lemma HasName.binder {a : Assoc i} {x : Atom α} :
    a.HasName x ↔ a.binder.HasName x
  := by aesop

  lemma HasName.name {a : Assoc i} {x : Atom α} :
    a.HasName x ↔ a.name.HasName x
  := by aesop

  @[simp]
  lemma HasName.comm {α : VarCat i} {a : Assoc i} {x : Atom α} :
    a.HasName x ↔ x.HasName a.name
  := by aesop

  @[aesop unsafe 20%]
  instance decidableHasName (a : Assoc i) {α : VarCat i} (x : Atom α) : Decidable (a.HasName x)
  := by
    cases Binder.decidableHasName a.binder x
    · case isFalse hasn'tName =>
      apply isFalse
      intros hasName
      cases hasName
        <;> simp [binder] at hasn'tName
    · case isTrue hasName =>
      apply isTrue
      cases a
        <;> simp [binder] at hasName
        <;> cases hasName
        <;> constructor
end Assoc

abbrev Env (i : CC) := AList (fun (v : Binder i) => Binding v.cat)

namespace Env
  def cons (Γ : Env i) (a : Assoc i) : Env i :=
    match a with
    | .val x T => AList.insert ⟨_, x⟩ (Binding.val T) Γ
    | .sub X S => AList.insert ⟨_, X⟩ (Binding.sub S) Γ
    | @Assoc.typ _ _ X T => AList.insert ⟨_, X⟩ (Binding.typ T) Γ

  infixl:70 " ▷ " => Env.cons

  def fold (f : α → Assoc i → α) (init : α) (Γ : Env i) : α :=
    List.foldr (fun s acc => f acc (Assoc.fromSigma s)) init Γ.entries

  def assocs (Γ : Env i) : List (Assoc i) :=
    Γ.entries.map Assoc.fromSigma

  def binders (Γ : Env i) : Finset (Binder i) :=
    Finset.mk (Multiset.ofList Γ.keys) Γ.nodupKeys

  def bindersList (Γ : Env i) : List (Binder i) :=
    Γ.keys

  def dom (Γ : Env i) {α : VarCat i} : Finset (Atom α) :=
    fold (· ∪ Assoc.dom ·) ∅ Γ

  def erase {α : VarCat i} (Γ : Env i) (x : Atom α) : Env i :=
    AList.erase ⟨α, x⟩ Γ

  @[simp]
  def cons_eq_iff :
    Γ ▷ a = Δ ▷ b ↔ erase Γ a.name = erase Δ b.name ∧ a = b
  := by
    apply Iff.intro
    · intros Eq
      simp [erase,AList.erase]
      simp [cons] at Eq
      cases a <;> rename_i x T <;> cases b <;> rename_i x' T'
        <;> simp [AList.insert] at Eq
        <;> obtain ⟨⟨Eq.x, Eq.T⟩, Eq.tl⟩ := Eq
        <;> simp [Assoc.binder]
      all_goals apply And.intro <;> aesop
    · intros Eqs
      obtain ⟨Eq.ctx, Eq.asc⟩ := Eqs
      simp [cons]
      cases a <;> rename_i x T <;> cases b <;> rename_i x' T'
        <;> cases Eq.asc
        <;> simp [AList.insert]
        <;> simp [erase,AList.erase] at Eq.ctx
        <;> exact Eq.ctx

  @[simp]
  def erase_cons_swap {α : VarCat i} {a : Assoc i} {x : Atom α} :
    ¬a.HasName x →
    erase (Γ ▷ a) x = erase Γ x ▷ a
  := by
    intros Neq
    apply AList.ext
    simp only [cons]
    cases α <;> cases a <;> rename_i y T
      <;> simp only [Assoc.type.match_1]
      <;> rw [AList.insert_entries]
      <;> simp only [erase,AList.erase]
      <;> simp only [AList.insert,List.kinsert]
      <;> rw [List.kerase_cons_ne (by aesop)]
      <;> rw [List.kerase_kerase]

  @[simp]
  lemma erase_nil :
    erase ∅ x = ∅
  := by rfl

  @[simp]
  lemma fold_nil :
    fold f z ∅ = z
  := by rfl

  @[simp]
  lemma fold_cons :
    fold f z (Γ ▷ a) = f (fold f z (erase Γ a.name)) a
  := by
    cases a <;> simp [fold,cons,erase,AList.erase,Assoc.binder]

  @[simp]
  lemma erase_cons_eq {i : CC} {Γ : Env i} {a : Assoc i} :
    erase (Γ ▷ a) a.name = erase Γ a.name
  := by
    cases a <;> rename_i x T <;> simp [erase,cons,AList.erase,Assoc.binder]

  @[simp]
  lemma erase_cons {i : CC} {α : VarCat i} {Γ : Env i} (a : Assoc i) {x : Atom α} :
    erase (Γ ▷ a) x =
      if a.HasName x then
        erase Γ x
      else
        erase Γ x ▷ a
  := by
    split
    · case inl hasName =>
      cases hasName <;> simp [erase,cons,AList.erase]
    · case inr hasn'tName =>
      cases a
        <;> simp only [erase,cons]
        <;> rw [AList.insert_erase]
        <;> simp
        <;> split
        <;> first | simp
                  | rename_i Eq.cat;
                    cases Eq.cat;
                    simp;
                    intros Eq.name;
                    cases Eq.name;
                    apply hasn'tName;
                    constructor

  lemma binder_mem_iff_name_mem_dom {α : VarCat i} {x : Atom α} :
    ⟨α, x⟩ ∈ Γ ↔ x ∈ dom Γ
  := by
    induction Γ using AList.insertRec
    · case H0 => simp [dom,assocs]
    · case IH w b Γ w.NotIn IH =>
      apply Iff.intro
      · case mp =>
        intros v.In
        cases v.In <;> simp only [dom,fold,assocs,List.map,List.foldr,Finset.mem_union]
        · case head =>
          apply Or.inr
          rw [Assoc.dom_fromSigma]
          simp
        · case tail v.In =>
          cases (decEq ⟨α, x⟩ w)
          · case isFalse neq =>
            apply Or.inl
            rw [List.kerase_of_not_mem_keys (by aesop)] at *
            apply IH.mp v.In
          · case isTrue eq =>
            apply Or.inr
            obtain ⟨β, y⟩ := w
            injection eq with eq.cat eq.name
            simp at b
            rw [eq.cat,eq.name,Assoc.dom_fromSigma]
            simp
      · case mpr =>
        intros v.In
        simp only [dom,assocs,fold,List.foldr,Finset.mem_union] at v.In
        simp
        cases v.In
        · case inl v.In =>
          cases (decEq ⟨α, x⟩ w)
          · case isFalse neq =>
            apply Or.inr
            rw [List.kerase_of_not_mem_keys (by aesop)] at v.In
            apply IH.mpr
            simp [dom,Finset.fold,AList.keys,List.keys]
            apply v.In
          · case isTrue eq =>
            rw [eq]
            apply Or.inl rfl
        · case inr v.In =>
          apply Or.inl
          obtain ⟨β, y⟩ := w
          simp at b
          simp only [Assoc.dom] at v.In
          rw [Assoc.binder_fromSigma_eq_fst] at v.In
          simp [Binder.dom] at v.In
          simp
          split
          · case inl Eq.cat =>
            simp [Eq.cat] at v.In
            cases Eq.cat
            exact v.In
          · case inr Neq.cat =>
            replace Neq.cat : β ≠ α := Neq.cat ∘ Eq.symm
            simp [Neq.cat] at v.In

  @[elab_as_elim]
  lemma rec_erase {motive : Env i → Sort}
    (nil : motive ∅)
    (cons : ∀ (Γ : Env i) (a : Assoc i),
      motive (erase Γ a.name) →
      motive (Γ ▷ a))
    : ∀ Γ, motive Γ
  := by
    intros Γ
    induction Γ using AList.insertRec
    · case H0 => exact nil
    · case IH v b Γ v.NotIn IH =>
      specialize cons Γ (Assoc.fromSigma ⟨v, b⟩)
      simp [erase,_root_.Env.cons] at cons
      obtain ⟨α, x⟩ := v
      cases b <;> simp [Assoc.binder] at cons
        <;> apply cons
        <;> rw [AList.erase_of_not_mem v.NotIn]
        <;> exact IH

  @[elab_as_elim]
  lemma rec_assoc {motive : Env i → Sort}
    (nil : motive ∅)
    (cons : ∀ (Γ : Env i) (a : Assoc i),
      a.name ∉ dom Γ →
      motive Γ →
      motive (Γ ▷ a))
    : ∀ Γ, motive Γ
  := by
    intros Γ
    induction Γ using AList.insertRec
    · case H0 =>
      exact nil
    · case IH v b Γ v.NotIn IH =>
      specialize cons Γ (Assoc.fromSigma ⟨v, b⟩)
      cases v; cases b
        <;> rw [Assoc.binder_fromSigma_eq_fst] at cons
        <;> simp only [_root_.Env.cons,Assoc.fromSigma,Assoc.binder] at cons
        <;> apply cons (binder_mem_iff_name_mem_dom.not.mp v.NotIn) IH

  @[elab_as_elim,eliminator]
  lemma rec_bindings {motive : Env i → Sort}
    (nil : motive ∅)
    (val : ∀ (x : Atom (.var i)) (T : Typ i) (Γ : Env i),
      x ∉ dom Γ →
      motive Γ →
      motive (Γ ▷ x ⦂ T))
    (sub : ∀ (X : Atom (.tvar i)) (T : Typ i) (Γ : Env i),
      X ∉ dom Γ →
      motive Γ →
      motive (Γ ▷ X <: T))
    (typ : ∀ (X : Atom (.tvar i)) (T : Typ i) (Γ : Env i),
      X ∉ dom Γ →
      motive Γ →
      motive (Γ ▷ X ≔ T))
    : ∀ Γ, motive Γ
  := by
    intros Γ
    induction Γ using rec_assoc
    · case nil => exact nil
    · case cons Γ a a.NotIn IH =>
      cases a
      · case val => apply val <;> aesop
      · case sub => apply sub <;> aesop
      · case typ => apply typ <;> aesop

  lemma dom_keys {α : VarCat i} {x : Atom α} {Γ : Env i} :
    x ∈ dom Γ ↔ ⟨α, x⟩ ∈ Γ.keys
  := by
    simp only [dom,fold,AList.keys]
    induction Γ.entries generalizing α
    · case nil => simp
    · case cons s Γ.entries IH =>
      simp only [List.foldr,List.keys,List.map]
      simp only [Finset.mem_union,List.mem_cons]
      apply Iff.intro
      · case mp =>
        intros x.In
        cases x.In
        · case inl x.In =>
          apply Or.inr
          apply IH.mp x.In
        · case inr x.In =>
          apply Or.inl
          obtain ⟨⟨β, y⟩, b⟩ := s
          simp only [Assoc.dom_fromSigma_def] at x.In
          simp
          split
          · case inl Eq.cat =>
            simp [Eq.cat] at x.In
            cases Eq.cat
            exact x.In
          · case inr Neq.cat =>
            simp [Neq.cat] at x.In
      · case mpr =>
        intros x.In
        cases x.In
        · case inl x.In =>
          apply Or.inr
          obtain ⟨⟨β, y⟩, b⟩ := s
          simp only [Assoc.dom_fromSigma_def]
          split
          · case inl Eq.cat =>
            simp [Eq.cat] at x.In
            cases Eq.cat
            simp
            exact x.In
          · case inr Neq.cat =>
            simp [Neq.cat] at x.In
        · case inr x.In =>
          apply Or.inl
          apply IH.mpr x.In

  @[simp]
  lemma dom_nil {α : VarCat i} : dom (α := α) ∅ = ∅
  := by simp [dom]

  lemma dom_cons_weak {Γ : Env i} {a : Assoc i} :
    dom (Γ ▷ a) (α := α) = dom (erase Γ a.name) ∪ Assoc.dom a
  := by simp [dom]

  @[simp]
  lemma erase_not_in_dom {Γ : Env i} {x : Atom α} :
    x ∉ dom Γ →
    erase Γ x = Γ
  := by
    intros x.NotIn
    simp [erase]
    rw [dom_keys] at x.NotIn
    apply AList.erase_of_not_mem x.NotIn

  lemma erase_commutative :
    erase (erase Γ x) y = erase (erase Γ y) x
  := by
    simp [erase]
    apply AList.erase_erase

  @[simp]
  lemma erase_in {Γ : Env i} {α β : VarCat i} {x : Atom α} {y : Atom β} :
    x ∈ dom (erase Γ y) ↔ x ∈ dom Γ ∧ ¬x.HasName y
  := by
    induction Γ <;> simp
    all_goals {
      rename_i z T Γ z.NotIn IH
      split
      · case inl hasName =>
        cases hasName
        all_goals {
          simp [dom_cons_weak,Assoc.name,Assoc.binder]
          rw [erase_not_in_dom z.NotIn] at *
          aesop
        }
      · case inr hasn'tName =>
        simp [dom_cons_weak,Assoc.name,Assoc.dom,Assoc.binder]
        rw [erase_commutative]
        rw [erase_not_in_dom z.NotIn]
        cases α <;> first | simp at hasn'tName
                          | aesop
    }

  lemma erase_notin {α β : VarCat i} {x : Atom α} {y : Atom β} :
    x ∉ dom Γ →
    x ∉ dom (erase Γ y)
  := by
    intros x.NotIn
    induction Γ using rec_assoc generalizing α β <;> simp
    case cons Γ a a.NotIn IH =>
    split
    · case inl hasName =>
      cases hasName
      simp only [dom_cons_weak] at x.NotIn
      aesop
    · case inr hasn'tName =>
      rw [dom_cons_weak] at *
      rw [erase_commutative]
      rw [erase_not_in_dom a.NotIn] at *
      simp at *
      intros x.In
      rcases x.In with ⟨x.In,x.hasn'tName⟩ | ⟨x.In⟩ <;> apply x.NotIn
      · exact Or.inl x.In
      · exact Or.inr x.In

  lemma dom_erase_subset {Γ : Env i} {α β : VarCat i} (x : Atom β) :
    dom (erase Γ x) (α := α) ⊆ dom Γ
  := by
    induction Γ
    · case nil => simp
    all_goals {
      rename_i y T Γ y.NotIn IH
      simp
      split
      · case inl hasName =>
        cases hasName
        rw [dom_cons_weak]
        simp
        apply Finset.subset_union_left
      · case inr hasn'tName =>
        simp only [dom_cons_weak,Assoc.name,Assoc.binder]
        rw [erase_commutative]
        rw [erase_not_in_dom y.NotIn]
        apply Finset.union_subset_union_left IH
    }

  @[simp]
  lemma dom_erase {Γ : Env i} {α β : VarCat i} {x : Atom β} :
    dom (erase Γ x) (α := α) =
      if h : α = β then
        dom Γ \ {h ▸ x}
      else
        dom Γ
  := by
    induction Γ using rec_assoc generalizing x
    · case nil => simp
    · case cons Γ a a.NotIn IH =>
      rw [dom_cons_weak]
      cases a <;> rename_i y T <;> simp at a.NotIn <;> simp
      all_goals {
        split
        · case inl hasName =>
          cases hasName
          rw [erase_not_in_dom a.NotIn]
          simp [Assoc.binder] at *
          split
          · case inl Eq.cat =>
            cases Eq.cat
            simp at *
            aesop
          · case inr Neq.cat =>
            cases α <;> simp; exfalso; exact Neq.cat rfl
        · case inr hasn'tName =>
          rw [
            dom_cons_weak,
            erase_commutative,
            erase_not_in_dom a.NotIn
          ]
          aesop
      }

  @[simp]
  lemma dom_cons {Γ : Env i} {a : Assoc i} :
    dom (Γ ▷ a) (α := α) = dom Γ ∪ Assoc.dom a
  := by
    rw [dom_cons_weak]
    simp [dom_erase]
    cases α <;> cases a <;> simp [Assoc.binder]

  @[simp]
  lemma dom_erase_different_cat {Γ : Env i} :
    α ≠ β →
    dom (α := β) (erase (α := α) Γ x) = dom Γ
  := by induction Γ <;> simp [erase_cons,Assoc.binder] <;> aesop

  instance instEmptyCollection : EmptyCollection (Env i) where
    emptyCollection := ∅

  instance instMembership : Membership (Assoc i) (Env i) :=
    ⟨fun a Γ => a ∈ Γ.assocs⟩

  @[simp]
  lemma not_mem_nil (a : Assoc i) :
    a ∉ (∅ : Env i)
  := by
    simp [EmptyCollection.emptyCollection,Membership.mem,assocs]
    intros a.In
    cases a.In

  @[simp]
  lemma assocs_nil :
    assocs (∅ : Env i) = ∅
  := by simp [assocs]

  @[simp]
  lemma assocs_cons :
    assocs (Γ ▷ a) = a :: assocs (erase Γ a.name)
  := by aesop

  @[simp]
  lemma assocs_erase {Γ : Env i} {x : Atom α} :
    assocs (erase Γ x) = List.eraseP
      (fun (a : Assoc i) => decide (a.HasName x))
      (assocs Γ)
  := by
    simp only [assocs]
    rw [List.eraseP_map]
    simp only [erase,AList.erase,List.kerase]
    congr
    ext a
    simp
    obtain ⟨v, b⟩ := a
    cases v; cases b <;> simp
    all_goals {
      rename_i T x
      split
      · rename_i Eq.cat
        cases Eq.cat
        simp
      · rename_i Neq.cat
        replace Neq.cat : _ ≠ α := Neq.cat ∘ Eq.symm
        simp [Neq.cat]
        intros hasName
        cases hasName
        exact Neq.cat rfl
    }

  @[simp]
  lemma mem_cons (a b : Assoc i) :
    a ∈ Γ ▷ b ↔ a ∈ erase Γ b.name ∨ a = b
  := by
    simp only [instMembership]
    rw [assocs_cons]
    simp only [assocs,erase,assocs_erase,AList.erase,List.kerase]
    aesop

  def concat (Γ : Env i) (Δ : Env i) : Env i :=
    Δ ∪ Γ

  instance instAppend : Append (Env i) where
    append := concat

  @[simp]
  lemma nil_concat {Γ : Env i} :
    ∅ ++ Γ = Γ
  := by simp [HAppend.hAppend,Append.append,concat]

  @[simp]
  lemma concat_nil {Γ : Env i} :
    Γ ++ ∅ = Γ
  := by rfl

  @[simp]
  lemma concat_singleton {Γ : Env i} :
    Γ ++ ∅ ▷ a = Γ ▷ a
  := by cases a <;> rfl

  @[simp]
  lemma concat_cons {Γ : Env i} :
    Γ ++ Δ ▷ a = (Γ ++ Δ) ▷ a
  := by cases a <;> simp [HAppend.hAppend,Append.append,concat,cons,Union.union,AList.union,AList.insert]

  @[simp]
  lemma erase_concat {Γ Δ : Env i} :
    erase (Γ ++ Δ) x = erase Γ x ++ erase Δ x
  := by
    simp [erase,HAppend.hAppend,Append.append,concat]
    rw [AList.union_erase]

  @[simp]
  lemma mem_erase_iff {Γ : Env i} {x : Atom α} {a : Assoc i} :
    a ∈ erase Γ x ↔ a ∈ Γ ∧ ¬a.HasName x
  := by
    induction Γ using rec_assoc <;> simp
    case cons Γ b b.NotIn IH =>
    split
    · case inl hasName =>
      cases hasName
      aesop
    · case inr hasn'tName =>
      rw [mem_cons]
      rw [erase_commutative]
      simp [erase_not_in_dom b.NotIn]
      aesop

  @[simp]
  lemma mem_in :
    a ∈ Γ →
    a.name ∈ dom Γ
  := by induction Γ <;> aesop

  @[simp]
  lemma mem_concat_iff {Γ Δ : Env i} :
    a ∈ Γ ++ Δ ↔ (a ∈ Γ ∧ a.name ∉ dom Δ) ∨ a ∈ Δ
  := by
    induction Δ using rec_assoc generalizing Γ
    · case nil => aesop
    · case cons Δ b b.NotIn IH =>
      apply Iff.intro
      · case mp =>
        simp
        rw [erase_not_in_dom b.NotIn]
        intros a.In
        cases a.In
        · case inl a.In =>
          rcases IH.mp a.In with ⟨a.InΓ,a.NotInΔ⟩ | ⟨a.InΔ⟩
          · cases decEq a b
            · case isFalse Neq =>
              apply Or.inl (And.intro _ _)
              · obtain ⟨a.InΓ, _⟩ := mem_erase_iff.mp a.InΓ
                apply a.InΓ
              · intros a.InΔb
                cases a.InΔb
                · case inl a.InΔ =>
                  exact a.NotInΔ a.InΔ
                · case inr a.EqB =>
                  cases a <;> cases b <;> rename_i x T y U <;> simp [Assoc.name,Assoc.dom,Assoc.binder] at a.EqB
                  all_goals {
                    cases a.EqB
                    simp at *
                  }
            · case isTrue a.Eq =>
              exact Or.inr (Or.inr a.Eq)
          · apply Or.inr (Or.inl (And.intro a.InΔ _))
            cases a <;> cases b <;> rename_i x T y U
              <;> simp [Assoc.name,Assoc.dom,Assoc.binder] at *
              <;> intros Eq
              <;> cases Eq
              <;> apply b.NotIn
              <;> exact mem_in a.InΔ
        · case inr a.Eq =>
          exact Or.inr (Or.inr a.Eq)
      · case mpr =>
        simp
        rw [erase_not_in_dom b.NotIn]
        intros a.In
        rcases a.In with ⟨a.InΓ, a.NotInΔ⟩ | ⟨⟨a.InΓ, a.NotInΔ⟩ | a.Eq⟩
        · cases decEq a b
          · case isFalse Neq =>
            apply Or.inl
            apply IH.mpr
            apply Or.inl
            apply And.intro
            · apply mem_erase_iff.mpr
              apply And.intro a.InΓ
              rw [Assoc.HasName.in_dom]
              intros a.NotB
              apply a.NotInΔ
              cases a <;> cases b <;> rename_i x T y U
                <;> simp [Assoc.name,Assoc.binder] at *
                <;> aesop
            · exact a.NotInΔ ∘ Or.inl
          · case isTrue Eq =>
            apply Or.inr Eq
        · cases a <;> cases b <;> rename_i x T y U
            <;> simp [Assoc.binder] at *
            <;> aesop
        · exact Or.inr a.Eq

  @[simp]
  lemma mem_cons_head {Γ : Env i} :
    a ∈ Γ ▷ a
  := by simp

  @[simp]
  lemma mem_cons_tail {Γ : Env i} :
    ¬a.HasName b.name →
    a ∈ Γ →
    a ∈ Γ ▷ b
  := by
    intros Neq a.In
    simp [mem_cons] at *
    apply Or.inl (And.intro a.In Neq)

  @[simp]
  lemma mem_concat_right {Γ Δ : Env i} :
    a ∈ Δ →
    a ∈ Γ ++ Δ
  := by induction Γ <;> aesop

  @[simp]
  lemma cons_not_nil {Γ : Env i} :
    Γ ▷ a ≠ ∅
  := by cases a <;> simp [cons,AList.insert,instEmptyCollection,AList.instEmptyCollectionAList]

  @[simp]
  lemma dom_concat {Γ Δ : Env i} :
    dom (α := α) (Γ ++ Δ) = dom Γ ∪ dom Δ
  := by
    induction Δ <;> simp [Assoc.dom,Assoc.binder]
    all_goals {
      rename_i IH
      split <;> simp [IH]
    }

  def Disjoint (Γ Δ : Env i) :=
    AList.Disjoint Γ Δ

  @[simp]
  lemma Disjoint_empty {Γ : Env i} :
    Disjoint Γ ∅
  := by simp [Disjoint,AList.Disjoint]

  @[simp]
  lemma Disjoint_comm {Γ Δ : Env i} :
    Disjoint Γ Δ ⇔ Disjoint Δ Γ
  := by
    simp [Disjoint,AList.Disjoint]
    aesop

  @[simp]
  lemma Disjoint

end Env

-/

attribute [irreducible] Env

@[simp] instance : EmptyCollection (Env i) := Env.instEmptyCollection
@[simp] instance : Membership (Assoc i) (Env i) := Env.instMembership
@[simp] instance : Append (Env i) := Env.instAppend
