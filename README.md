# LeanDecisionTheory

project to formalize decision theory under risk and ambiguity, and the epistemic foundations of game theory,
in Lean 4 via Mathlib.

Mathlib has no decision theory in the preference-axiomatic sense. It has no lotteries, no
preference relations, no expected-utility representation, no capacities and no Choquet
integral. What it has is `Mathlib/Probability/Decision/`, which is Wald-style
*statistical* decision theory — risk, Bayes risk, `minimaxRisk` — a different subject. The one
formalisation of the von Neumann–Morgenstern theorem in the literature is a standalone paper,
not a library. So the representation theorems that every applied model quietly invokes have
never been machine-checked in a form anyone can import.

starting with foundations: **Gilboa–Schmeidler maxmin representation**

## Status

scaffold. skeleton compiles; theorems are stated and marked `sorry -- TODO:`. Lots to do

| Component | State |
|---|---|
| `Priors.lean` — the simplex of priors, convex and compact | proved |
| `Functional/Niveloid.lean` — concave niveloids, their core | proved |
| `Functional/MinRepresentation.lean` — minimum-of-expectations duality | easy direction proved, representation open |
| `AnscombeAumann/Act.lean` — acts, mixtures, utility acts | proved |
| `AnscombeAumann/Axioms.lean` — the six Gilboa–Schmeidler axioms | stated, basic consequences proved |
| `AnscombeAumann/MaxMin.lean` — the representation theorem | stated, open |

## Roadmap

1. **Maxmin expected utility on a finite state space** — the current target.
   Anscombe–Aumann acts, the six axioms, and the representation
   `f ≽ g ↔ min_{p ∈ C} 𝔼_p[u ∘ f] ≥ min_{p ∈ C} 𝔼_p[u ∘ g]` with `C` unique.
   The proof decomposes into a von Neumann–Morgenstern step on constant acts, a reduction to a
   functional on state-contingent payoffs, and a convex-duality step; see the proof plan in
   `AnscombeAumann/MaxMin.lean`.
2. **Capacities and the Choquet integral**, then Schmeidler's CEU representation. Nothing of
   this exists anywhere in Lean.
3. **General state spaces** — a sure-thing-bounded payoff space and finitely additive priors,
   replacing the finite-dimensional separation argument with a weak-\* one. Milestone 1 is
   deliberately finite: it is where the economics lives and it needs no Banach-space duality.
4. **Variational and smooth-ambiguity preferences** (Maccheroni–Marinacci–Rustichini;
   Klibanoff–Marinacci–Mukerji), which are the same duality with the minimum perturbed.
5. **Belief hierarchies and type spaces** — the epistemic-foundations direction. Mathlib is
   unexpectedly well prepared here: Polish spaces, standard Borel spaces, projective families
   and Ionescu–Tulcea are all in place, which is what the Mertens–Zamir universal type space
   needs.

## Building

requires [elan](https://github.com/leanprover/elan). The toolchain is pinned in `lean-toolchain`
and the Mathlib revision in `lakefile.toml`.

```
lake exe cache get   # Mathlib's compiled oleans, once
lake build
```

`lake build` reports `declaration uses 'sorry'` for the open theorems. That is expected while
the status table above has open entries, and it is the only warning the build should produce.

## Conventions

- **no silent `sorry`.** An incomplete proof is written `sorry -- TODO: <what remains>`, so that
  grepping for `sorry` finds a description of the gap. No axioms are declared.
- **Mathlib naming**: `lowerCamelCase` for definitions, `snake_case` for theorems, American
  spelling. Everything lives in the `DecisionTheory` namespace.
- **state definitions /w generality economists use**, not the maximum Lean permits. The
  state space is finite in milestone 1 because that is the case the literature applies.
- **preference is `≽`.** Throughout, `pref f g` means *`f` is weakly preferred to `g`*.
- **distinct mathematics from the decision theory.** `Functional/` contains statements with
  no preferences in them, so they can be upstreamed to Mathlib on their own; see `UPSTREAM.md`.
- **please make sure you understand your ai-generated code** Proofs may be drafted with AI
  assistance, but nothing is committed until the person committing it can explain every line:
  what each hypothesis is doing, why each step follows, and what would break if a hypothesis
  were dropped. A proof that compiles and is not understood is worse than no proof, because it
  cannot be maintained, generalised, or trusted when Mathlib moves underneath it. Disclose AI
  assistance in the commit message or PR description.
- **Commit messages, issues and review comments are handwritten.** They are the record of why
  a change was made and they are how a reader judges whether the author understood the change. This also keeps the repository compliant
  with Mathlib's contribution policy, which requires AI assistance to be disclosed, bars
  LLM-written comments on GitHub and Zulip, and expects the submitter to understand every line
  — anything destined for `UPSTREAM.md` must satisfy it. Thank you!

## References

- F. J. Anscombe and R. J. Aumann, *A Definition of Subjective Probability*, Annals of
  Mathematical Statistics 34 (1963), 199–205.
- I. Gilboa and D. Schmeidler, *Maxmin expected utility with non-unique prior*, Journal of
  Mathematical Economics 18 (1989), 141–153.
- D. Schmeidler, *Subjective probability and expected utility without additivity*,
  Econometrica 57 (1989), 571–587.
- F. Maccheroni, M. Marinacci and A. Rustichini, *Ambiguity aversion, robustness, and the
  variational representation of preferences*, Econometrica 74 (2006), 1447–1498.
- E. Dekel and M. Siniscalchi, *Epistemic Game Theory*, Handbook of Game Theory vol. 4 (2015) —
  the target list for milestone 5.
- For the von Neumann–Morgenstern step, there is a formalisation precedent:
  *From Axioms to Algorithms: Mechanized Proofs of the vNM Utility Theorem*,
  [arXiv:2506.07066](https://arxiv.org/abs/2506.07066).

## Related work

- [EconCSLib](https://github.com/gametheoryinlean/EconCSLib) — strategic, extensive and
  coalitional games, social choice, fair division, matching, auctions, mechanism design. This
  repository deliberately sits *below* it: preferences and beliefs rather than solution
  concepts. Interoperability is a goal, duplication is not.
- [LeanEconomics](https://github.com/LeanEconomics/LeanEconomics) — recursive macroeconomics
  and the algorithms that solve quantitative models.
- [AgreeToDisagree](https://github.com/AxiomMath/AgreeToDisagree) — Aumann's agreement theorem,
  with the partition and posterior infrastructure milestone 5 would build on.

## License

Apache 2.0, matching Mathlib. See `LICENSE`.
