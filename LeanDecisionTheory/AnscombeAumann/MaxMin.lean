/-
Copyright (c) 2026 Niel Bezrookove. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Niel Bezrookove
-/
module

public import LeanDecisionTheory.AnscombeAumann.Axioms
public import LeanDecisionTheory.Functional.MinRepresentation

/-!
# gilboa–schmeidler maxmin representation

The target of this development. A preference relation over Anscombe–Aumann acts satisfies the
six axioms of `IsGilboaSchmeidler` if and only if there are an affine utility index `u` on
consequences and a nonempty closed convex set `C` of priors such that acts are ranked by

  `min {p ∈ C} 𝔼_p [u ∘ f]`,

and `C` is unique. The decision maker behaves as if entertaining a *set* of beliefs and
evaluating every act by its worst case over that set; `C` is a singleton exactly when
certainty independence can be strengthened back to full independence.

## Main definitions

* `DecisionTheory.MaxMinRepresents` : the representation property, as a predicate on a utility
  index and a set of priors.

## Main results

* `DecisionTheory.exists_maxMin_representation` : the hard direction. **Open.**
* `DecisionTheory.isGilboaSchmeidler_of_maxMinRepresents` : the easy direction. **Open**, but
  it is only bookkeeping on top of `IsConcaveNiveloid.of_isLeast_expect`, which is proved.
* `DecisionTheory.maxMin_core_unique` : uniqueness of the set of priors. **Open.**

## Proof plan

The decomposition the file is built around, and the reason `Functional/` exists separately:

1. Restricted to constant acts the axioms are the von Neumann–Morgenstern axioms, so there is
   an affine `u : M →ᵃ[ℝ] ℝ` representing preference over sure consequences. *This is the one
   step with a formalization precedent — see the vNM paper cited in `README.md` — and it is the
   step to do first.*
2. Monotonicity makes preference depend on an act only through its utility act
   `Act.utility u f : S → ℝ`, so preference descends to a relation on `S → ℝ`.
3. The certainty equivalent of a utility act defines `I : (S → ℝ) → ℝ`. Weak order and
   Archimedean continuity make it well defined; monotonicity makes it monotone; certainty
   independence makes it constant-additive and positively homogeneous; uncertainty aversion
   makes it superadditive. So `I` is an `IsConcaveNiveloid`.
4. `isLeast_expect_core` turns `I` into a minimum of expectations over `core I`, which is the
   representation, with `C = core I`.

Step 4 is pure convex duality and lives in `Functional/MinRepresentation.lean`. Steps 1–3 are
the decision theory. Keeping them apart is what makes step 4 upstreamable to Mathlib on its
own; see `UPSTREAM.md`.
-/

@[expose] public section

namespace DecisionTheory

variable {S M : Type*} [Fintype S] [AddCommGroup M] [Module ℝ M]

def MaxMinRepresents (pref : Act S M → Act S M → Prop) (u : M →ᵃ[ℝ] ℝ) (C : Set (S → ℝ)) :
    Prop :=
  ∀ f g : Act S M,
    pref f g ↔ sInf ((fun p => expect p (Act.utility u g)) '' C)
      ≤ sInf ((fun p => expect p (Act.utility u f)) '' C)

/-- **gilboa–schmeidler theorem**, hard: the axioms produce a utility index and a
set of priors. -/
theorem exists_maxMin_representation [Nonempty S]
    {pref : Act S M → Act S M → Prop} (h : IsGilboaSchmeidler pref) :
    ∃ (u : M →ᵃ[ℝ] ℝ) (C : Set (S → ℝ)), C.Nonempty ∧ C ⊆ Priors S ∧ Convex ℝ C ∧ IsClosed C ∧
      MaxMinRepresents pref u C :=
  sorry -- TODO: steps 1-4 of the proof plan above; start with step 1, von Neumann-Morgenstern
        -- on constant acts

/-- **gilboa–schmeidler theorem**, easy: a maxmin ranking satisfies the axioms. -/
theorem isGilboaSchmeidler_of_maxMinRepresents [Nonempty S]
    {pref : Act S M → Act S M → Prop} {u : M →ᵃ[ℝ] ℝ} {C : Set (S → ℝ)}
    (hne : C.Nonempty) (hC : C ⊆ Priors S) (hu : ∃ m m' : M, u m ≠ u m')
    (hrep : MaxMinRepresents pref u C) : IsGilboaSchmeidler pref :=
  sorry -- TODO: each axiom from the corresponding property of `IsConcaveNiveloid`, which
        -- `IsConcaveNiveloid.of_isLeast_expect` already supplies; `Act.utility_mix` is the
        -- bridge from mixtures of acts to mixtures of payoffs

theorem maxMin_core_unique [Nonempty S]
    {pref : Act S M → Act S M → Prop} {u : M →ᵃ[ℝ] ℝ} {C D : Set (S → ℝ)}
    (hC : C ⊆ Priors S) (hCconv : Convex ℝ C) (hCclosed : IsClosed C)
    (hD : D ⊆ Priors S) (hDconv : Convex ℝ D) (hDclosed : IsClosed D)
    (hrepC : MaxMinRepresents pref u C) (hrepD : MaxMinRepresents pref u D) : C = D :=
  sorry -- TODO: both represent the same functional; apply `core_eq_of_isLeast` twice

end DecisionTheory
