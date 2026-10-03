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

/-- a function dominating `I` pointwise is automatically a prior -/
theorem mem_priors_of_dominates (hI : IsConcaveNiveloid I) {p : S → ℝ}
    (hdom : ∀ x, I x ≤ expect p x) : p ∈ Priors S := by
  classical
  refine ⟨fun s => ?_, ?_⟩
  · have h0 : (0 : S → ℝ) ≤ Pi.single s 1 := by
      intro t
      rcases eq_or_ne t s with rfl | h
      · simp
      · simp [h]
    calc (0 : ℝ) = I 0 := hI.map_zero.symm
      _ ≤ I (Pi.single s 1) := hI.mono h0
      _ ≤ expect p (Pi.single s 1) := hdom _
      _ = p s := expect_single p s
  · have hge : (1 : ℝ) ≤ ∑ s, p s := by
      have h := hdom 1
      rwa [hI.normalized, expect_one] at h
    have hle : ∑ s, p s ≤ 1 := by
      have h := hdom (fun _ => (-1 : ℝ))
      rw [hI.map_const] at h
      have hneg : expect p (fun _ => (-1 : ℝ)) = -∑ s, p s := by
        simp only [expect, mul_neg, mul_one, Finset.sum_neg_distrib]
      rw [hneg] at h
      linarith
    linarith

/-- concave niveloid has supergradient at every point -/
theorem exists_supergradient (hI : IsConcaveNiveloid I) (a : S → ℝ) :
    ∃ p : S → ℝ, (∀ x, I x ≤ expect p x) ∧ expect p a = I a :=
  sorry -- TODO: separate `(a, I a)` from the hypograph `{(x, t) | t ≤ I x}` in `(S → ℝ) × ℝ`.
        -- Convex by `hI.concave`, closed because `hI.le_add_const` makes `I` nonexpansive. The
        -- separating functional's last coordinate is strictly negative (the hypograph is
        -- unbounded downwards), so rescaling gives `q` with `I x ≤ I a + expect q (x - a)`.
        -- Then `x := 0` and `x := 2 • a` with `hI.posHom` force `expect q a = I a`.

theorem isLeast_expect_core_of_supergradient (hI : IsConcaveNiveloid I) {a p : S → ℝ}
    (hdom : ∀ x, I x ≤ expect p x) (heq : expect p a = I a) :
    IsLeast ((fun q => expect q a) '' core I) (I a) := by
  refine ⟨⟨p, ⟨mem_priors_of_dominates hI hdom, hdom⟩, heq⟩, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  exact hq.2 a

theorem isLeast_expect_core (hI : IsConcaveNiveloid I) (a : S → ℝ) :
    IsLeast ((fun p => expect p a) '' core I) (I a) :=
  let ⟨_p, hdom, heq⟩ := exists_supergradient hI a
  isLeast_expect_core_of_supergradient hI hdom heq

theorem core_nonempty (hI : IsConcaveNiveloid I) : (core I).Nonempty :=
  let ⟨p, hdom, _⟩ := exists_supergradient hI 1
  ⟨p, mem_priors_of_dominates hI hdom, hdom⟩

theorem eq_sInf_expect_core (hI : IsConcaveNiveloid I) (a : S → ℝ) :
    I a = sInf ((fun p => expect p a) '' core I) :=
  ((isLeast_expect_core hI a).csInf_eq).symm

theorem subset_core_of_isLeast {C : Set (S → ℝ)} (hC : C ⊆ Priors S)
    (hrep : ∀ a, IsLeast ((fun p => expect p a) '' C) (I a)) : C ⊆ core I :=
  fun p hp => ⟨hC hp, fun a => (hrep a).2 ⟨p, hp, rfl⟩⟩

theorem core_eq_of_isLeast (hI : IsConcaveNiveloid I) {C : Set (S → ℝ)}
    (hC : C ⊆ Priors S) (hconv : Convex ℝ C) (hclosed : IsClosed C)
    (hrep : ∀ a, IsLeast ((fun p => expect p a) '' C) (I a)) : C = core I :=
  sorry -- TODO: `subset_core_of_isLeast` gives `C ⊆ core I`. For the reverse, separate a
        -- `p ∈ core I \ C` from the compact convex `C` to get a direction `a` with
        -- `expect p a < expect q a` for all `q ∈ C`, hence `expect p a < I a`, contradicting
        -- `p ∈ core I`.

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
