import CCDeconstructed.Syntax
import CCDeconstructed.Classes
import CCDeconstructed.Infrastructure.Var

open Scoped FreeVariables VarCat

namespace Cap
  @[aesop norm]
  def fv (C : Cap i) : Finset (Atom (var i)) :=
    C.fold (· ∪ ·) ∅ Var.fv

  lemma mem_free_iff_mem_fv :
    .free x ∈ C ↔ x ∈ fv C
  := by
    induction' C using Finset.induction <;> aesop

  @[aesop safe apply]
  lemma mem_free_implies_mem_fv :
    .free x ∈ C → x ∈ fv C
  := Iff.mp mem_free_iff_mem_fv

  lemma mem_fv_implies_mem_free :
    x ∈ fv C → .free x ∈ C
  := Iff.mpr mem_free_iff_mem_fv

  @[aesop norm]
  def bv (C : Cap i) : Finset (Index (var i)) :=
    C.fold (· ∪ ·) ∅ Var.bv

  lemma mem_bound_iff_mem_bv :
    .bound k ∈ C ↔ k ∈ bv C
  := by
    induction' C using Finset.induction <;> aesop

  @[aesop safe apply]
  lemma mem_bound_implies_mem_bv :
    .bound k ∈ C → k ∈ bv C
  := Iff.mp mem_bound_iff_mem_bv

  lemma mem_bv_implies_mem_bound :
    k ∈ bv C → .bound k ∈ C
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
    ∀ v ∈ C, Var.WellScopedRec (allowCap := true) n v

  @[aesop norm 5]
  def WellScoped (C : Cap i) :=
    ∀ v ∈ C, Var.WellScoped (allowCap := true) v

  @[aesop safe forward]
  lemma WellScoped_implies_WellScopedRec_0 :
    WellScoped C →
    WellScopedRec 0 C
  := by aesop

  @[simp,aesop safe forward]
  lemma WellScopedRec_weaken :
    m <= n →
    WellScopedRec m C →
    WellScopedRec n C
  := by
    intros leq C.WS v v.In
    apply Var.WellScopedRec_weaken <;> aesop

  instance instWellScopednessInfrastructure : WellScopedness.Infrastructure (Cap i) where
    WellScopedRec := WellScopedRec
    WellScoped := WellScoped
    WellScoped_implies_WellScopedRec_0 := WellScoped_implies_WellScopedRec_0
    WellScopedRec_weaken := WellScopedRec_weaken

  lemma substitute_fresh :
    x ∉ fv C →
    substitute C x u = C
  := by
    simp [substitute]
    intros x.NotIn x.In
    exfalso; apply x.NotIn
    apply mem_free_implies_mem_fv x.In

  @[simp]
  lemma WellScopedRec_instantiateRec :
    WellScopedRec n (instantiateRec C n u) →
    WellScopedRec (n + 1) C
  := by
    intros C.WS v v.WS
    apply Var.WellScopedRec_instantiateRec (u := u)
    apply C.WS
    simp only [instantiateRec]
    aesop

  @[simp]
  lemma instantiateRec_WellScopedRec :
    WellScopedRec n C →
    k >= n →
    instantiateRec C k u = C
  := by aesop

  @[simp]
  instance instScopedInfrastructure : Scoped.Infrastructure (Cap i) (var i) where
    instantiateRec := instantiateRec
    substitute := substitute
    substitute_fresh := substitute_fresh
    WellScopedRec_instantiateRec := WellScopedRec_instantiateRec
    instantiateRec_WellScopedRec := instantiateRec_WellScopedRec

  instance instEmptyCollection : EmptyCollection (Cap i) := inferInstance
  instance instSingleton : Singleton (Var (.var i)) (Cap i) := inferInstance
  instance instMembership : Membership (Var (.var i)) (Cap i) := inferInstance
end Cap
