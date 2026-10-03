/-
Copyright (c) 2026 Niel Bezrookove. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Niel Bezrookove
-/
module

public import LeanDecisionTheory.Priors

/-!
# Static games, beliefs, and rational choice

The objects everything later is built from. Perea, *Epistemic Game Theory: Reasoning and Choice*
(Cambridge, 2012), §2.1–2.3, p13–24; his section numbers are cited throughout. Strict dominance
(§2.5) and belief in the opponents' rationality (§2.6) are separate topics and get their own
files.

Standing assumptions from his Chapter 1, which the rest of the book never restates: games are
finite (p8), utility functions are transparent to all players so beliefs range over choices
only and never over payoffs (p8), and players never randomize — a randomized choice appears in
§2.5 purely as a proof device, not as an object of choice (p7).
-/

@[expose] public section

namespace DecisionTheory.Epistemic

/-! ## Static games (§2.1, §2.3)

static game: every player makes one choice without observing any opponent's choice, and the
utility of each player depends on the choices of all. Perea introduces two players first and
generalises in 2.3; the definition here is the general one. -/

/-- finite static game. -/
structure StaticGame where
  /-- players. -/
  Player : Type
  /-- choices available to each player. -/
  Choice : Player → Type
  /-- What each player gets from a combination of choices. -/
  utility : (i : Player) → (∀ j, Choice j) → ℝ
  [playerFintype : Fintype Player]
  [playerDecEq : DecidableEq Player]
  [choiceFintype : ∀ i, Fintype (Choice i)]

attribute [instance] StaticGame.playerFintype StaticGame.playerDecEq StaticGame.choiceFintype

namespace StaticGame

variable (G : StaticGame) (i : G.Player)

/-- combination of the opponents' choices, as in 2.3: one choice for every player but `i`. -/
def OppChoices : Type := ∀ j : {j : G.Player // j ≠ i}, G.Choice j

instance : Fintype (G.OppChoices i) := Pi.instFintype

/-- full choice combination obtained when `i` chooses `c` and the opponents choose `d`. -/
def profile (c : G.Choice i) (d : G.OppChoices i) : ∀ j, G.Choice j :=
  fun j => if h : j = i then h.symm ▸ c else d ⟨j, h⟩

@[simp]
theorem profile_self (c : G.Choice i) (d : G.OppChoices i) : G.profile i c d i = c := by
  simp [profile]

theorem profile_of_ne (c : G.Choice i) (d : G.OppChoices i) {j : G.Player} (h : j ≠ i) :
    G.profile i c d j = d ⟨j, h⟩ := by
  simp [profile, h]

/-- 2.1: belief for player `i` is probability distribution on the opponents' choice
combinations. beliefs in 2.1 are degenerate, assigning probability one to a
single combination. probabilistic beliefs of 2.2 are the general case, and only the general
case is defined here -/
abbrev Belief : Type := {b : G.OppChoices i → ℝ // b ∈ Priors (G.OppChoices i)}

/-! ## Expected utility and rational choice (§2.2)

"rational" via Perea: optimal under *some* belief. made explicit (p5–6)
that the belief itself may be wholly unreasonable -/

/-- expected utility of choice `c` for player `i` under the belief `b`. -/
noncomputable def expectedUtility (b : G.Belief i) (c : G.Choice i) : ℝ :=
  expect b.1 fun d => G.utility i (G.profile i c d)

/-- choice c is *optimal* under a belief if no choice does better against it -/
def IsOptimal (b : G.Belief i) (c : G.Choice i) : Prop :=
  ∀ c' : G.Choice i, G.expectedUtility i b c' ≤ G.expectedUtility i b c

/-- 2.1: choice c is *rational* if it is optimal for some belief about the opponents'
choices -/
def IsRational (c : G.Choice i) : Prop :=
  ∃ b : G.Belief i, G.IsOptimal i b c

theorem isRational_of_isOptimal {b : G.Belief i} {c : G.Choice i} (h : G.IsOptimal i b c) :
    G.IsRational i c :=
  ⟨b, h⟩

/-- optimality: over a finite, nonempty choice set some choice maximises expected
utility, so every belief supports at least one rational choice. -/
theorem exists_isOptimal [Nonempty (G.Choice i)] (b : G.Belief i) :
    ∃ c : G.Choice i, G.IsOptimal i b c := by
  obtain ⟨c, _, hc⟩ :=
    Finset.exists_max_image Finset.univ (G.expectedUtility i b) ⟨Classical.arbitrary _, by simp⟩
  exact ⟨c, fun c' => hc c' (Finset.mem_univ c')⟩

theorem exists_isRational [Nonempty (G.Choice i)] [Nonempty (G.OppChoices i)] :
    ∃ c : G.Choice i, G.IsRational i c := by
  classical
  obtain ⟨d⟩ := ‹Nonempty (G.OppChoices i)›
  obtain ⟨c, hc⟩ := G.exists_isOptimal i ⟨Pi.single d 1, single_mem_priors d⟩
  exact ⟨c, _, hc⟩

end StaticGame

end DecisionTheory.Epistemic
