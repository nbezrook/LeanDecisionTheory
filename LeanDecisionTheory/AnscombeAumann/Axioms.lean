/-
Copyright (c) 2026 Niel Bezrookove. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Niel Bezrookove
-/
module

public import LeanDecisionTheory.AnscombeAumann.Act

/-!
# gilboa–schmeidler axioms

Six conditions on a preference relation over Anscombe–Aumann acts. Five of them are the
Anscombe–Aumann axioms for subjective expected utility with independence weakened, and the
sixth — uncertainty aversion — is what replaces the strength that was removed.

Throughout, `pref f g` is read **`f` is weakly preferred to `g`**, so `pref` is `≽` and not
`≼`. Indifference and strict preference are derived (`Pref.indiff`, `Pref.strict`).

## The axioms

* `weakOrder` : `pref` is total and transitive. Completeness of comparison.
* `cIndep` : **certainty independence.** Mixing both acts with the *same constant* act, in the
  same proportion, leaves the comparison unchanged. Full independence would allow mixing with
  an arbitrary act; restricting to constants is exactly the weakening that admits ambiguity
  aversion, because mixing with a constant cannot hedge.
* `archimedean` : a continuity condition — if `f` beats `g` beats `h`, then some mixture of `f`
  and `h` beats `g` and some other mixture is beaten by it.
* `monotone` : if the consequence of `f` is weakly preferred to that of `g` state by state,
  then `f` is weakly preferred to `g`. Statewise dominance.
* `uncAversion` : **uncertainty aversion.** If the decision maker is indifferent between `f`
  and `g`, they weakly prefer any mixture of the two. Hedging between equally good bets cannot
  hurt; this is the preference form of concavity.
* `nondegenerate` : not everything is indifferent to everything else, so the representation is
  not vacuous.
-/

@[expose] public section

namespace DecisionTheory

variable {S M : Type*} [AddCommGroup M] [Module ℝ M]

namespace Pref

variable (pref : Act S M → Act S M → Prop)

def indiff (f g : Act S M) : Prop := pref f g ∧ pref g f

def strict (f g : Act S M) : Prop := pref f g ∧ ¬ pref g f

end Pref

/-- gilboa–Schmeidler axioms on a preference relation over anscombe–aumann acts, where
`pref f g` means that `f` is weakly preferred to `g`. -/
structure IsGilboaSchmeidler (pref : Act S M → Act S M → Prop) : Prop where
  total : ∀ f g, pref f g ∨ pref g f
  trans : ∀ {f g h}, pref f g → pref g h → pref f h
  cIndep : ∀ (f g : Act S M) (m : M) {α : ℝ}, 0 < α → α ≤ 1 →
    (pref f g ↔ pref (Act.mix α f (Act.const m)) (Act.mix α g (Act.const m)))
  archimedean : ∀ {f g h : Act S M}, Pref.strict pref f g → Pref.strict pref g h →
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ Pref.strict pref (Act.mix α f h) g) ∧
      (∃ β : ℝ, 0 < β ∧ β < 1 ∧ Pref.strict pref g (Act.mix β f h))
  monotone : ∀ f g : Act S M, (∀ s, pref (Act.const (f s)) (Act.const (g s))) → pref f g
  uncAversion : ∀ (f g : Act S M) {α : ℝ}, 0 ≤ α → α ≤ 1 →
    Pref.indiff pref f g → pref (Act.mix α f g) f
  nondegenerate : ∃ f g : Act S M, Pref.strict pref f g

namespace IsGilboaSchmeidler

variable {pref : Act S M → Act S M → Prop} (h : IsGilboaSchmeidler pref)
include h

theorem refl (f : Act S M) : pref f f := (h.total f f).elim id id

theorem indiff_refl (f : Act S M) : Pref.indiff pref f f := ⟨h.refl f, h.refl f⟩

theorem of_not (f g : Act S M) (hg : ¬ pref g f) : pref f g := (h.total f g).elim id (absurd · hg)

omit [AddCommGroup M] [Module ℝ M] h in
theorem indiff_symm {f g : Act S M} (hfg : Pref.indiff pref f g) : Pref.indiff pref g f :=
  ⟨hfg.2, hfg.1⟩

theorem strict_irrefl (f : Act S M) : ¬ Pref.strict pref f f := fun hs => hs.2 (h.refl f)

theorem indiff_of_forall_indiff (f g : Act S M)
    (hs : ∀ s, Pref.indiff pref (Act.const (f s)) (Act.const (g s))) : Pref.indiff pref f g :=
  ⟨h.monotone f g fun s => (hs s).1, h.monotone g f fun s => (hs s).2⟩

end IsGilboaSchmeidler

end DecisionTheory
