# Candidates for upstreaming to Mathlib

Checked against Mathlib master `282fbb865d53622ef7f9ef29f6763a0327ee6b5f` (2 October 2026).
Record the check with each entry so it can be redone when Mathlib moves.

## Candidate

### 1. A concave niveloid is a minimum of expectations — `Functional/MinRepresentation.lean`

```
isLeast_expect_core :
  IsConcaveNiveloid I → IsLeast ((fun p => expect p a) '' core I) (I a)
```

A monotone, constant-additive, positively homogeneous, superadditive, normalised functional on
`S → ℝ` with `S` finite is the pointwise minimum of expectations over a compact convex set of
probability vectors, and the minimum is attained. This is convex duality with no decision theory
in it, which is why `Functional/` is kept separate from `AnscombeAumann/`.

**What Mathlib has.** The separation machinery (`geometric_hahn_banach_point_closed` and
friends in `Mathlib/Analysis/LocallyConvex/Separation.lean`), Krein–Milman
(`Mathlib/Analysis/Convex/KreinMilman.lean`), cone duality (`Mathlib/Analysis/Convex/Cone/Dual.lean`),
and the standard simplex with its convexity and compactness.

**What Mathlib does not have.** No support-function representation of a concave positively
homogeneous functional, and no notion of a niveloid. Checked by grepping master for
`supportFunction`, `niveloid`, `Choquet` and `capacity`: no hits outside unrelated files.

**Before a PR.** Three things.

- The statement should probably be for a general finite index type and `𝕜`-valued with
  `[LinearOrderedField 𝕜]`, or stated as the support function of a convex set so that the
  simplex plays no special role. Decide which form a reviewer wants before writing it up.
- `Priors` must go. It duplicates Mathlib's standard simplex; it exists here only because
  Mathlib is mid-migration — `stdSimplex 𝕜 ι` was deprecated on 2026-08-29 in favour of a
  bundled `StdSimplex` type (`Mathlib/Geometry/Convex/ConvexSpace/`). `Priors` is defined so
  that the swap is a one-line change, and should be made once the new API settles.
- `ConstAdditive`, `PosHomogeneous` and `Superadditive` are local names for notions Mathlib may
  already have under other names — check `Mathlib/Analysis/Convex/Function.lean` and the
  sublinear/gauge files (`Gauge.lean`, `EGauge.lean`) before introducing them upstream.

## Not upstreamable

The Anscombe–Aumann layer — acts, the Gilboa–Schmeidler axioms, `MaxMinRepresents` — is stated
in terms of preference relations. That is the right shape for decision theory and the wrong
shape for Mathlib.
