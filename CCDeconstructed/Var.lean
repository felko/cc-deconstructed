import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice

import CCDeconstructed.CC

inductive VarCat : CC -> Type where
  | var i : VarCat i
  | tvar i : VarCat i
  deriving Repr, DecidableEq

open VarCat

@[aesop norm 0]
abbrev Index (_ : VarCat i) := Nat
abbrev Atom (_ : VarCat i) := Nat

namespace Atom
  def freshFor (set : Finset (Atom α)) : ∃ (x : Atom α), x ∉ set := by
    cases Finset.decidableNonempty
    · case isFalse notNonempty =>
      exists 0
      contrapose! notNonempty
      exists 0
    · case isTrue nonempty =>
      cases Finset.max_of_nonempty nonempty
      rename_i max eq
      exists max + 1
      apply Finset.not_mem_of_max_lt (b := max)
      · simp
      · exact eq

  instance instDecidableEq : DecidableEq (Atom α) := inferInstance

  def coerce (x : Atom α) : Atom β := x
end Atom

attribute [irreducible] Atom

instance : DecidableEq (Atom α) := Atom.instDecidableEq

@[aesop unsafe [constructors 10%,cases 20%]]
inductive Var (α : VarCat i) : Type where
  | free : Atom α -> Var α
  | bound : Index α -> Var α
  | cap {_ : α = var i} : Var α

instance : DecidableEq (Var α) := by
  intros u v
  cases u <;> cases v
    <;> (try apply isFalse; intros eq; injection eq <;> fail)
    <;> (try case cap.cap; apply isTrue; rfl)
    <;> (rename_i x y; cases (decEq x y); rename_i H)
    <;> (try simp [H]; constructor; simp)
    <;> (apply isTrue; simp; assumption)
