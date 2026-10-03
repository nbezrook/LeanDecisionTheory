/-
Copyright (c) 2026 Niel Bezrookove. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Niel Bezrookove
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Priors on a finite state space

A *prior* on a finite state space `S` is a probability vector: a nonnegative function
`p : S → ℝ` summing to one. `Priors S` is the set of them.

This is the standard simplex. Mathlib has it twice over: `stdSimplex 𝕜 ι`, deprecated since
2026-08-29, and the bundled replacement `StdSimplex`. We define it locally while that migration
settles, so that nothing here has to move twice; see `UPSTREAM.md`. The definition is stated so
that the swap is a one-line change.

## Main definitions

* `DecisionTheory.Priors S` : the probability vectors on `S`.
* `DecisionTheory.expect p a` : the expectation `∑ s, p s * a s` of `a` under `p`.

## Main results

* `DecisionTheory.convex_priors`, `DecisionTheory.isCompact_priors` : the prior set is convex
  and compact, which is what makes the minimum in a maxmin representation attained.
-/

@[expose] public section

open Set Finset

namespace DecisionTheory

variable {S : Type*} [Fintype S]

def Priors (S : Type*) [Fintype S] : Set (S → ℝ) :=
  {p | (∀ s, 0 ≤ p s) ∧ ∑ s, p s = 1}

def expect (p a : S → ℝ) : ℝ := ∑ s, p s * a s

@[simp]
theorem mem_priors_iff {p : S → ℝ} : p ∈ Priors S ↔ (∀ s, 0 ≤ p s) ∧ ∑ s, p s = 1 := Iff.rfl

theorem nonneg_of_mem_priors {p : S → ℝ} (hp : p ∈ Priors S) (s : S) : 0 ≤ p s := hp.1 s

theorem sum_eq_one_of_mem_priors {p : S → ℝ} (hp : p ∈ Priors S) : ∑ s, p s = 1 := hp.2

theorem le_one_of_mem_priors {p : S → ℝ} (hp : p ∈ Priors S) (s : S) : p s ≤ 1 := by
  rw [← hp.2]
  exact Finset.single_le_sum (fun t _ => hp.1 t) (Finset.mem_univ s)

theorem single_mem_priors [DecidableEq S] (s : S) : (Pi.single s 1 : S → ℝ) ∈ Priors S := by
  refine ⟨fun t => ?_, by simp⟩
  rcases eq_or_ne t s with rfl | h
  · simp
  · simp [h]

theorem priors_nonempty [Nonempty S] : (Priors S).Nonempty := by
  classical
  exact ⟨_, single_mem_priors (Classical.arbitrary S)⟩

/-! ### Expectation -/

@[simp]
theorem expect_const {p : S → ℝ} (hp : p ∈ Priors S) (c : ℝ) :
    expect p (fun _ => c) = c := by
  show ∑ s, p s * c = c
  rw [← Finset.sum_mul, hp.2, one_mul]

theorem expect_add (p a b : S → ℝ) : expect p (a + b) = expect p a + expect p b := by
  simp only [expect, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem expect_smul (t : ℝ) (p a : S → ℝ) : expect p (t • a) = t * expect p a := by
  simp only [expect, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

@[simp]
theorem expect_one (p : S → ℝ) : expect p 1 = ∑ s, p s := by
  simp [expect]

/-- expectation of a point mass reads off coordinate -/
@[simp]
theorem expect_single [DecidableEq S] (p : S → ℝ) (s : S) :
    expect p (Pi.single s 1) = p s := by
  simp only [expect, Pi.single_apply, mul_ite, mul_one, mul_zero]
  simp

theorem expect_mono {p : S → ℝ} (hp : p ∈ Priors S) {a b : S → ℝ} (hab : a ≤ b) :
    expect p a ≤ expect p b :=
  Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hab s) (hp.1 s)

theorem expect_add_const {p : S → ℝ} (hp : p ∈ Priors S) (a : S → ℝ) (c : ℝ) :
    expect p (a + fun _ => c) = expect p a + c := by
  rw [expect_add, expect_const hp]


theorem convex_priors : Convex ℝ (Priors S) := by
  rintro p ⟨hp0, hp1⟩ q ⟨hq0, hq1⟩ a b ha hb hab
  refine ⟨fun s => ?_, ?_⟩
  · simpa using add_nonneg (mul_nonneg ha (hp0 s)) (mul_nonneg hb (hq0 s))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp1, hq1, mul_one, mul_one,
      hab]

theorem isClosed_priors : IsClosed (Priors S) := by
  have h₁ : IsClosed {p : S → ℝ | ∀ s, 0 ≤ p s} := by
    have heq : {p : S → ℝ | ∀ s, 0 ≤ p s} = ⋂ s, {p : S → ℝ | 0 ≤ p s} := by
      ext p; simp
    rw [heq]
    exact isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)
  have h₂ : IsClosed {p : S → ℝ | ∑ s, p s = 1} :=
    isClosed_eq (continuous_finsetSum _ fun s _ => continuous_apply s) continuous_const
  exact h₁.inter h₂

theorem priors_subset_pi_Icc : Priors S ⊆ Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1 :=
  fun _ hp s _ => ⟨hp.1 s, le_one_of_mem_priors hp s⟩

theorem isCompact_priors : IsCompact (Priors S) :=
  IsCompact.of_isClosed_subset
    (isCompact_univ_pi fun _ => isCompact_Icc) isClosed_priors priors_subset_pi_Icc

end DecisionTheory
