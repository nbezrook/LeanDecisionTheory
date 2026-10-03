/-
Copyright (c) 2026 Niel Bezrookove. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Niel Bezrookove
-/
module

public import LeanDecisionTheory.Priors

/-!
# Concave niveloids on a finite state space

A functional `I : (S → ℝ) → ℝ` assigns a certainty equivalent to a state-contingent payoff.
The four properties below are what the Gilboa–Schmeidler axioms deliver, and they are exactly
what is needed to represent `I` as a minimum of expectations:

* **monotone**: more payoff in every state is not worse;
* **constant additivity**: adding a sure amount `c` adds `c` to the certainty equivalent;
* **positive homogeneity**: scaling a payoff scales its certainty equivalent;
* **superadditivity**: `I a + I b ≤ I (a + b)`, the functional form of uncertainty aversion.

Positive homogeneity together with superadditivity makes `I` *superlinear*, i.e. concave and
positively homogeneous; with monotonicity and `I 1 = 1` this is the "concave niveloid" of the
decision-theory literature.

## Main definitions

* `DecisionTheory.IsConcaveNiveloid` : the bundle of the four properties plus normalisation.
* `DecisionTheory.core` : the priors that dominate `I` everywhere — the candidate set of beliefs.

## Main results

* `DecisionTheory.IsConcaveNiveloid.map_const` : `I` sends the sure payoff `c` to `c`.
* `DecisionTheory.IsConcaveNiveloid.concave` : superlinearity gives concavity.
* `DecisionTheory.isCompact_core`, `DecisionTheory.convex_core` : the core is compact and convex.
-/

@[expose] public section

open Set Finset

namespace DecisionTheory

variable {S : Type*} [Fintype S] {I : (S → ℝ) → ℝ}

def ConstAdditive (I : (S → ℝ) → ℝ) : Prop :=
  ∀ (a : S → ℝ) (c : ℝ), I (a + fun _ => c) = I a + c

def PosHomogeneous (I : (S → ℝ) → ℝ) : Prop :=
  ∀ (a : S → ℝ) {t : ℝ}, 0 ≤ t → I (t • a) = t * I a

def Superadditive (I : (S → ℝ) → ℝ) : Prop :=
  ∀ a b : S → ℝ, I a + I b ≤ I (a + b)

structure IsConcaveNiveloid (I : (S → ℝ) → ℝ) : Prop where
  mono : Monotone I
  constAdd : ConstAdditive I
  posHom : PosHomogeneous I
  superadd : Superadditive I
  normalized : I 1 = 1

namespace IsConcaveNiveloid

variable (hI : IsConcaveNiveloid I)
include hI

omit [Fintype S] in
theorem map_zero : I 0 = 0 := by
  have h := hI.posHom 0 (le_refl (0 : ℝ))
  rwa [zero_smul, zero_mul] at h

omit [Fintype S] in
theorem map_const (c : ℝ) : I (fun _ => c) = c := by
  have h := hI.constAdd 0 c
  rwa [zero_add, hI.map_zero, zero_add] at h

omit [Fintype S] in
theorem le_add_const {a b : S → ℝ} {c : ℝ} (hab : a ≤ b + fun _ => c) : I a ≤ I b + c :=
  (hI.mono hab).trans_eq (hI.constAdd b c)

omit [Fintype S] in
theorem concave : ∀ (a b : S → ℝ) {s t : ℝ}, 0 ≤ s → 0 ≤ t → s + t = 1 →
    s * I a + t * I b ≤ I (s • a + t • b) := by
  intro a b s t hs ht _
  calc s * I a + t * I b = I (s • a) + I (t • b) := by
        rw [hI.posHom a hs, hI.posHom b ht]
    _ ≤ I (s • a + t • b) := hI.superadd _ _

end IsConcaveNiveloid

def core (I : (S → ℝ) → ℝ) : Set (S → ℝ) :=
  {p ∈ Priors S | ∀ a : S → ℝ, I a ≤ expect p a}

@[simp]
theorem mem_core_iff {p : S → ℝ} :
    p ∈ core I ↔ p ∈ Priors S ∧ ∀ a : S → ℝ, I a ≤ expect p a := Iff.rfl

theorem core_subset_priors : core I ⊆ Priors S := fun _ hp => hp.1

theorem convex_core : Convex ℝ (core I) := by
  rintro p ⟨hpP, hp⟩ q ⟨hqP, hq⟩ s t hs ht hst
  refine ⟨convex_priors hpP hqP hs ht hst, fun a => ?_⟩
  have key : expect (s • p + t • q) a = s * expect p a + t * expect q a := by
    simp only [expect, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => by ring
  rw [key]
  calc I a = s * I a + t * I a := by rw [← add_mul, hst, one_mul]
    _ ≤ s * expect p a + t * expect q a := by
        gcongr
        exacts [hp a, hq a]

theorem isClosed_core : IsClosed (core I) := by
  have h : IsClosed {p : S → ℝ | ∀ a : S → ℝ, I a ≤ expect p a} := by
    have heq : {p : S → ℝ | ∀ a : S → ℝ, I a ≤ expect p a}
        = ⋂ a : S → ℝ, {p : S → ℝ | I a ≤ expect p a} := by
      ext p; simp
    rw [heq]
    refine isClosed_iInter fun a => isClosed_le continuous_const ?_
    exact continuous_finsetSum _ fun s _ => (continuous_apply s).mul continuous_const
  exact isClosed_priors.inter h

theorem isCompact_core : IsCompact (core I) :=
  isCompact_priors.of_isClosed_subset isClosed_core core_subset_priors

end DecisionTheory
