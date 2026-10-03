/-
Copyright (c) 2026 Niel Bezrookove. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Niel Bezrookove
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!
# Anscombe–Aumann acts

An *act* assigns to each state of the world an object of choice that can be mixed — in
Anscombe and Aumann's setting, a lottery over outcomes. We take the mixable objects to be
elements of a real vector space `M`, so that the mixture `α m + (1 - α) m'` is just the module
structure, and lotteries are the special case where `M` is the space of finitely supported
signed measures and attention is restricted to the simplex inside it. Nothing below needs that
restriction, so nothing below imposes it.

Acts are then functions `S → M` and mix *pointwise*, which is the single structural fact the
Anscombe–Aumann axioms exploit: mixtures of acts and mixtures of outcomes interact.

## Main definitions

* `DecisionTheory.Act S M` : acts on the state space `S` with consequences in `M`.
* `DecisionTheory.Act.const m` : the constant act, which is how a sure consequence enters the
  preference order.
* `DecisionTheory.Act.mix α f g` : the pointwise mixture `α • f + (1 - α) • g`.
* `DecisionTheory.Act.utility u f` : the state-contingent payoff `fun s => u (f s)` induced by a
  utility index `u`.
-/

@[expose] public section

namespace DecisionTheory

variable {S M : Type*}

abbrev Act (S M : Type*) := S → M

namespace Act

def const (m : M) : Act S M := fun _ => m

@[simp]
theorem const_apply (m : M) (s : S) : (const m : Act S M) s = m := rfl

variable [AddCommGroup M] [Module ℝ M]

def mix (α : ℝ) (f g : Act S M) : Act S M := α • f + (1 - α) • g

@[simp]
theorem mix_apply (α : ℝ) (f g : Act S M) (s : S) :
    mix α f g s = α • f s + (1 - α) • g s := rfl

@[simp]
theorem mix_zero (f g : Act S M) : mix 0 f g = g := by
  ext s; simp [mix]

@[simp]
theorem mix_one (f g : Act S M) : mix 1 f g = f := by
  ext s; simp [mix]

@[simp]
theorem mix_self (α : ℝ) (f : Act S M) : mix α f f = f := by
  ext s
  simp only [mix_apply, ← add_smul, show α + (1 - α) = (1 : ℝ) by ring, one_smul]

theorem mix_comm (α : ℝ) (f g : Act S M) : mix α f g = mix (1 - α) g f := by
  ext s
  simp only [mix_apply, sub_sub_cancel]
  exact add_comm _ _

theorem mix_const (α : ℝ) (m m' : M) :
    mix α (const m) (const m') = (const (α • m + (1 - α) • m') : Act S M) := by
  ext s; simp [mix, const]

def utility (u : M →ᵃ[ℝ] ℝ) (f : Act S M) : S → ℝ := fun s => u (f s)

@[simp]
theorem utility_apply (u : M →ᵃ[ℝ] ℝ) (f : Act S M) (s : S) : utility u f s = u (f s) := rfl

@[simp]
theorem utility_const (u : M →ᵃ[ℝ] ℝ) (m : M) :
    utility u (const m : Act S M) = fun _ => u m := rfl

theorem utility_mix (u : M →ᵃ[ℝ] ℝ) {α : ℝ} (f g : Act S M) :
    utility u (mix α f g) = α • utility u f + (1 - α) • utility u g := by
  ext s
  simpa only [utility_apply, mix_apply, Pi.add_apply, Pi.smul_apply] using
    Convex.combo_affine_apply (f := u) (show α + (1 - α) = (1 : ℝ) by ring)

end Act

end DecisionTheory
