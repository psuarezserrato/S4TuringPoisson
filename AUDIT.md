# Independent Audit of the S4TuringPoisson Formalization (main @ c530a68)

Auditor: Claude Sonnet 5.5, run directly against the repo (not relying on worker reports).

## Verdict
- **Sound**: yes. Kernel-level checks pass.
- **Complete**: **no**, relative to MISSION_DIRECTIVE.md §1. Two substantive gaps below.

## What was verified (my own checks)
| Check | Result |
|---|---|
| `lake build --wfail` on root | 9411/9411 jobs, 0 errors, 0 warnings |
| `sorry/admit/axiom/unsafe/implemented_by/native_decide/opaque/maxHeartbeats` in code (comments stripped), all 16 files | none |
| `Lean.collectAxioms` over every non-internal `S4TuringPoisson.*` declaration | **1717 declarations, 0 with axioms outside {propext, Classical.choice, Quot.sound}** |
| `#print axioms` on all Main.lean headline theorems | standard axioms only |
| `set_option` usage | only `linter.concreteInstances false` (14x); no weakened soundness options |
| `IsTuringComplete` design | non-vacuous: `encodePoint` depends on `(M,t)`, `encodeOpen` on `(M,k,w)` and is nonempty, computable 2^-m approximation required, no `by_cases` on halting |

Note: workers reported "2,808 declarations"; my count of non-internal declarations is 1,717. The difference is counting method (auxiliary/internal names), not a soundness issue.

## Gap 1 — Turing completeness is conditional, never discharged
- `exists_turingComplete_volumePreserving_poissonDiffeomorph_S4`, `..._diffeomorph_S4`, `..._fourManifold`, `undecidable_orbit_reachability_S4`, all `*_of_cmpp`, and the Gate-6 checks hold only under `[HasTuringCompleteAreaPreservingDiskIsotopy]` / `[HasCMPPCantorCirculationHamiltonians]`.
- **No instance of either class exists anywhere in the project.** So these theorems have never been applied to an actual map; their consistency is not demonstrated in Lean.
- `HasCMPPCantorCirculationHamiltonians` asks for a finite list of compactly supported Hamiltonians whose time-one map equals a generalized shift *exactly* on the whole Cantor set (`RealizesGeneralizedShiftByHamiltonians`). This is the real content of CMPP21 Thm 5.2 and is assumed, not proved.
- The only unconditional diffeomorphism (`s4UnconditionalPoissonDiffeomorph`) is a sector swap: leaf-, volume-, and Poisson-preserving and `≠ id`, but **not** Turing complete.
- Directive §1.3 allowed this as an explicit class only as an upstream-literature fallback; the stretch track (M3.3) did not close it.

## Gap 2 — The S^4 fibration is not the ADK fibration
- `s4Fibration x = southPoleStereoInv (x0, x1)`: image is a cap of S^2; the critical locus is the circle `{x2=x3=x4=0}` where fibres collapse to points (definite-fold type).
- The paper's ADK fibration has T^2/S^2 fibres and indefinite quadratic singularities. Eq. (2) (`indefiniteFoldMap`), real Lefschetz, and wrinkled-cusp models are proved in `LocalSingularModels.lean` but **are not used by any global fibration or class**.
- `WrinkledFibration` has no constraint on singularity type (only: smooth map, regular trivialized disk region). The name overstates it. `AdmitsWrinkledOrBrokenLefschetzFibration` therefore assumes only "a smooth map with such a region", and Gay–Kirby/Lekili existence is assumed, not proved (permitted by the directive).
- The directive text did suggest this S^4 example, and Theorem 1 as literally stated is satisfied. The statement is mathematically fine; it is just not the paper's construction.

## Not checked
- I did not re-derive the ~19.5k lines line by line. Mathematical faithfulness beyond the definitions/statements above rests on the build, axiom audit, and the worker/verifier checks. Authors and verifiers were the same model family, so they are not fully independent.

## To reach "complete"
1. Prove or construct an instance of `HasCMPPCantorCirculationHamiltonians` (formalize CMPP21 Thm 5.2 smoothing).
2. Optionally glue the ADK local model into a global S^4 fibration and constrain `WrinkledFibration` to wrinkled/Lefschetz singularities.
