/-
Copyright (c) 2026 Niel Bezrookove. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Niel Bezrookove
-/
module

public import LeanDecisionTheory.Functional.Niveloid

/-!
# A concave niveloid is a minimum of expectations

The mathematical core of the maxmin representation, with no decision theory in it: a monotone,
constant-additive, superlinear, normalised functional on `S → ℝ` is the pointwise minimum of the
expectations taken over its core,

  `I a = min {expect p a | p ∈ core I}`,

and the minimum is attained. This is convex duality — `I` is concave and positively homogeneous,
so it is the support function (from below) of a convex compact set, and monotonicity plus
normalisation put that set inside the simplex.

Stated as `IsLeast` rather than with `⨅` deliberately: `IsLeast` carries both halves at once,
that `I a` *is* one of the expectations (attainment, which is what the economics uses) and that
it is a lower bound for all of them.

## Main results

* `DecisionTheory.core_nonempty` : the core is nonempty. Separating hyperplane.
* `DecisionTheory.isLeast_expect_core` : the representation.
* `DecisionTheory.IsConcaveNiveloid.of_isLeast_expect` : the converse, which is the easy
  direction and is proved here.

## Implementation notes

The finite state space is doing real work: the core lives in `S → ℝ`, finite-dimensional, so
separation needs only `geometric_hahn_banach_point_closed` and no weak-* topology, and the
minimum is attained by compactness of the core rather than by a Banach–Alaoglu argument. The
general case — a sure-thing-bounded payoff space and finitely additive priors — is milestone 3
in `README.md`.
-/

@[expose] public section

open Set Finset

namespace DecisionTheory

variable {S : Type*} [Fintype S] {I : (S → ℝ) → ℝ}

theorem isLeast_expect_core [Nonempty S] (hI : IsConcaveNiveloid I) (a : S → ℝ) :
    IsLeast ((fun p => expect p a) '' core I) (I a) :=
  sorry -- TODO: lower bound is `mem_core_iff`; attainment needs a supergradient of `I` at `a`

theorem eq_sInf_expect_core [Nonempty S] (hI : IsConcaveNiveloid I) (a : S → ℝ) :
    I a = sInf ((fun p => expect p a) '' core I) :=
  ((isLeast_expect_core hI a).csInf_eq).symm

theorem core_eq_of_isLeast [Nonempty S] (hI : IsConcaveNiveloid I) {C : Set (S → ℝ)}
    (hC : C ⊆ Priors S) (hconv : Convex ℝ C) (hclosed : IsClosed C)
    (hrep : ∀ a, IsLeast ((fun p => expect p a) '' C) (I a)) : C = core I :=
  sorry -- TODO: both inclusions by separation; `hrep` gives `C ⊆ core I` directly

theorem IsConcaveNiveloid.of_isLeast_expect {C : Set (S → ℝ)} (hC : C ⊆ Priors S)
    (hrep : ∀ a, IsLeast ((fun p => expect p a) '' C) (I a)) :
    IsConcaveNiveloid I where
  mono := by
    intro a b hab
    obtain ⟨⟨q, hq, hqb⟩, _⟩ := hrep b
    calc I a ≤ expect q a := (hrep a).2 ⟨q, hq, rfl⟩
      _ ≤ expect q b := expect_mono (hC hq) hab
      _ = I b := hqb
  constAdd := by
    intro a c
    obtain ⟨⟨p, hp, hpa⟩, hlb⟩ := hrep a
    obtain ⟨⟨q, hq, hqa⟩, hlb'⟩ := hrep (a + fun _ => c)
    have hpa' : expect p a = I a := hpa
    refine le_antisymm ?_ ?_
    · calc I (a + fun _ => c) ≤ expect p (a + fun _ => c) := hlb' ⟨p, hp, rfl⟩
        _ = expect p a + c := expect_add_const (hC hp) a c
        _ = I a + c := by rw [hpa']
    · calc I a + c ≤ expect q a + c := by gcongr; exact hlb ⟨q, hq, rfl⟩
        _ = expect q (a + fun _ => c) := (expect_add_const (hC hq) a c).symm
        _ = I (a + fun _ => c) := hqa
  posHom := by
    intro a t ht
    obtain ⟨⟨p, hp, hpa⟩, hlb⟩ := hrep a
    obtain ⟨⟨q, hq, hqa⟩, hlb'⟩ := hrep (t • a)
    have hpa' : expect p a = I a := hpa
    refine le_antisymm ?_ ?_
    · calc I (t • a) ≤ expect p (t • a) := hlb' ⟨p, hp, rfl⟩
        _ = t * expect p a := expect_smul t p a
        _ = t * I a := by rw [hpa']
    · calc t * I a ≤ t * expect q a := mul_le_mul_of_nonneg_left (hlb ⟨q, hq, rfl⟩) ht
        _ = expect q (t • a) := (expect_smul t q a).symm
        _ = I (t • a) := hqa
  superadd := by
    intro a b
    obtain ⟨⟨q, hq, hqab⟩, _⟩ := hrep (a + b)
    calc I a + I b ≤ expect q a + expect q b :=
          add_le_add ((hrep a).2 ⟨q, hq, rfl⟩) ((hrep b).2 ⟨q, hq, rfl⟩)
      _ = expect q (a + b) := (expect_add q a b).symm
      _ = I (a + b) := hqab
  normalized := by
    obtain ⟨⟨p, hp, hp1⟩, _⟩ := hrep 1
    rw [← hp1]
    show ∑ s, p s * (1 : S → ℝ) s = 1
    simpa using (hC hp).2

end DecisionTheory
