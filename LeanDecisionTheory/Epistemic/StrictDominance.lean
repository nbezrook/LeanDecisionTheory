/-
Copyright (c) 2026 Niel Bezrookove. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Niel Bezrookove
-/
module

public import LeanDecisionTheory.Epistemic.StaticGame

/-!
# Strictly dominated choices

per perea, 2.5, p30–37: choice c is *rational* exactly when no other choice, and no randomized
choice, beats it against every combination of the opponents' choices (2.5.3)

randomized choice c is not an object of choice here. Perea is explicit (p7, p32) that players
never randomize, and that randomized choices enter only as a device for identifying irrational
choices. therefore the separate name from `belief`, which is also a distribution but means
something else entirely
-/

@[expose] public section

namespace DecisionTheory.Epistemic

namespace StaticGame

variable (G : StaticGame) (i : G.Player)

/-! ## Randomized choices (2.5.1) -/

/-- 2.5.1(a): a distribution over one's own choices. A proof device, not an object
of choice. -/
abbrev RandomizedChoice : Type := {r : G.Choice i → ℝ // r ∈ Priors (G.Choice i)}

/-- 2.5.1(b): what a randomized choice yields against a fixed combination of the
opponents' choices. -/
noncomputable def randUtility (r : G.RandomizedChoice i) (d : G.OppChoices i) : ℝ :=
  expect r.1 fun c => G.utility i (G.profile i c d)

/-- randomized choice that picks `c` outright. -/
noncomputable def dirac [DecidableEq (G.Choice i)] (c : G.Choice i) : G.RandomizedChoice i :=
  ⟨Pi.single c 1, single_mem_priors c⟩

@[simp]
theorem randUtility_dirac [DecidableEq (G.Choice i)] (c : G.Choice i) (d : G.OppChoices i) :
    G.randUtility i (G.dirac i c) d = G.utility i (G.profile i c d) := by
  simp [randUtility, dirac]

/-! ## Strict dominance (2.5.2) -/

/-- 2.5.2(a). -/
def StrictlyDominatedBy (c c' : G.Choice i) : Prop :=
  ∀ d : G.OppChoices i, G.utility i (G.profile i c d) < G.utility i (G.profile i c' d)

/-- 2.5.2(b). -/
def StrictlyDominatedByRand (c : G.Choice i) (r : G.RandomizedChoice i) : Prop :=
  ∀ d : G.OppChoices i, G.utility i (G.profile i c d) < G.randUtility i r d

/-- 2.5.2(c). -/
def IsStrictlyDominated (c : G.Choice i) : Prop :=
  (∃ c', G.StrictlyDominatedBy i c c') ∨ (∃ r, G.StrictlyDominatedByRand i c r)

theorem strictlyDominatedByRand_dirac [DecidableEq (G.Choice i)] {c c' : G.Choice i}
    (h : G.StrictlyDominatedBy i c c') : G.StrictlyDominatedByRand i c (G.dirac i c') := by
  intro d
  rw [randUtility_dirac]
  exact h d

/-- 2.5.2 (a): special case of (b) at a point mass, so being
strictly dominated is being strictly dominated by a randomized choice. keep the two
apart for exposition. -/
theorem isStrictlyDominated_iff_exists_rand [DecidableEq (G.Choice i)] {c : G.Choice i} :
    G.IsStrictlyDominated i c ↔ ∃ r, G.StrictlyDominatedByRand i c r := by
  constructor
  · rintro (⟨c', hc'⟩ | h)
    · exact ⟨_, G.strictlyDominatedByRand_dirac i hc'⟩
    · exact h
  · exact Or.inr

/-! ## Characterisation of rational choices (2.5.3) -/

/-- averaging a randomized choice against a belief, in the two orders. The expected utility of
`r` under `b` is the `r`-average of the expected utilities of the pure choices. -/
theorem expect_randUtility (b : G.Belief i) (r : G.RandomizedChoice i) :
    expect b.1 (fun d => G.randUtility i r d)
      = expect r.1 (fun c => G.expectedUtility i b c) := by
  simp only [randUtility, expectedUtility, expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

/-- A randomized choice never beats the best pure choice against a given belief. -/
theorem expect_expectedUtility_le [Nonempty (G.Choice i)] (b : G.Belief i)
    (r : G.RandomizedChoice i) :
    ∃ c, expect r.1 (fun c' => G.expectedUtility i b c') ≤ G.expectedUtility i b c := by
  obtain ⟨c, hc⟩ := G.exists_isOptimal i b
  refine ⟨c, ?_⟩
  calc expect r.1 (fun c' => G.expectedUtility i b c')
      ≤ expect r.1 (fun _ => G.expectedUtility i b c) := expect_mono r.2 fun c' => hc c'
    _ = G.expectedUtility i b c := expect_const r.2 _

/-- 2.5.3: a strictly dominated choice is irrational.
Against any belief the dominating randomized choice does strictly better, because a pointwise
strict inequality survives averaging (`expect_lt_expect`); and it does no better than the best
pure choice. So the dominated choice is beaten by some pure choice under every belief. -/
theorem not_isRational_of_isStrictlyDominated [Nonempty (G.Choice i)] [DecidableEq (G.Choice i)]
    {c : G.Choice i} (hdom : G.IsStrictlyDominated i c) : ¬ G.IsRational i c := by
  rw [isStrictlyDominated_iff_exists_rand] at hdom
  obtain ⟨r, hr⟩ := hdom
  rintro ⟨b, hopt⟩
  have hlt : G.expectedUtility i b c < expect b.1 (fun d => G.randUtility i r d) :=
    expect_lt_expect b.2 fun d => hr d
  rw [expect_randUtility] at hlt
  obtain ⟨c', hc'⟩ := G.expect_expectedUtility_le i b r
  exact absurd (hopt c') (not_le.mpr (hlt.trans_le hc'))

/-- 2.5.3, proved by Perea in 2.9: a choice that is optimal under no
belief is strictly dominated by a randomized choice. -/
theorem isRational_of_not_isStrictlyDominated [Nonempty (G.Choice i)] [DecidableEq (G.Choice i)]
    {c : G.Choice i} (h : ¬ G.IsStrictlyDominated i c) : G.IsRational i c :=
  sorry -- TODO: the separating hyperplane on the simplex. The set of expected-utility vectors
        -- achievable by randomized choices is convex and compact in `OppChoices i → ℝ`; if `c`
        -- is dominated by none of them, the vector it induces is not strictly below any of
        -- them, and separating it from that set produces the belief under which `c` is
        -- optimal. Same duality as `Functional.exists_supergradient`; see also EconCSLib's
        -- `Math/LinearAlgebra/Farkas.lean`.

/-- **2.5.3**: the rational choices are exactly those that are neither strictly
dominated by another choice nor by a randomized choice. -/
theorem isRational_iff_not_isStrictlyDominated [Nonempty (G.Choice i)]
    [DecidableEq (G.Choice i)] {c : G.Choice i} :
    G.IsRational i c ↔ ¬ G.IsStrictlyDominated i c :=
  ⟨fun hrat hdom => G.not_isRational_of_isStrictlyDominated i hdom hrat,
    G.isRational_of_not_isStrictlyDominated i⟩

end StaticGame

end DecisionTheory.Epistemic
