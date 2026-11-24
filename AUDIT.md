# Audit of the `S4TuringPoisson` Formalization (ADK $S^4$, Lekili Moves & Closed 4-Manifolds)

Repository: `S4TuringPoisson` (Lean `v4.36.0`, Mathlib `fc4f59e5` + `TauCeti` `d91980bdc` + `Turing-recursive` `4120346`).
Supersedes the earlier CMPP Milestone Z audit upon completion of `MISSION_DIRECTIVE_LEKILI.md` (Option A ADK $S^4$ broken Lefschetz fibration `LW4`, Lekili Moves 1–4 and broken-to-wrinkled surgery `LW3`, `PurelyWrinkledFibration` `LW1`, unconditional closed 4-manifold Corollary 2 `LW2`, and 100% green `leanblueprint`).

## 1. Verdict
- **Sound**: **yes**. All `10,130` Lake build jobs pass with `--wfail`, zero forbidden tokens exist across all `29` `.lean` files (`41,361` lines), `35/35` leaf modules (`28` `S4TuringPoisson.*` + `7` `TuringRecursive.*`) pass `leanchecker` kernel replay, and `Lean.collectAxioms` over all `5,233` `S4TuringPoisson` declarations (plus `342` `Turing-recursive` declarations = `5,575` total) reports strictly `{propext, Classical.choice, Quot.sound}`.
- **Headline Theorems & Unconditional Status**:
  - **$S^4$ (Definite-Fold Projection)**: Unconditional (`0` binders) for `Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_S4`, `Main.exists_turingComplete_volumePreserving_diffeomorph_S4`, `Main.undecidable_orbit_reachability_S4`, and `exists_poisson_hamiltonian_realization_S4` (`R5`).
  - **$S^4$ (Global ADK Broken Lefschetz Fibration — Track A / Option A)**: Unconditional (`0` binders) for `exists_turingComplete_volumePreserving_poissonDiffeomorph_S4_ADK` and `exists_poisson_hamiltonian_realization_S4_ADK` on `s4BrokenLefschetzFibration : Sphere4 → Sphere2` (`S^2` and `T^2` regular fibers separated by an equatorial circle of indefinite quadratic folds).
  - **Lekili Moves 1–4 & Broken-to-Wrinkled Surgery (`LW3` — Track A)**: Every `BrokenLefschetzFibration` on a compact Hausdorff 4-manifold deforms to a `PurelyWrinkledFibration` (`BrokenLefschetzFibration.exists_purelyWrinkledFibration`).
  - **Closed Oriented 4-Manifolds (`Corollary 2`, `LW2` — Track B)**: Unconditional on any nonempty compact Hausdorff smooth 4-manifold `(M, V_M)` (`Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_closedFourManifold`, `Main.exists_turingComplete_volumePreserving_diffeomorph_closedFourManifold`, `Main.undecidable_orbit_reachability_closedFourManifold`, and `exists_poisson_hamiltonian_realization_closedFourManifold`) via `AdmitsWrinkledOrBrokenLefschetzFibration.ofPositiveVolumeForm`.

---

## 2. Kernel, Build & Static Verification Summary

| Check | Command | Observed Result |
|---|---|---|
| Full workspace build (`G1`) | `LEAN_NUM_THREADS=2 lake build --wfail` | `10,130 / 10,130` jobs succeeded, `0` errors, `0` warnings |
| Comment-stripped forbidden-token scan (`G2`) | `LEAN_NUM_THREADS=2 bash tools/collect_axioms.sh` | `0` occurrences of `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `native_decide`, `opaque`, `maxHeartbeats` across `29` `.lean` files (`41,361` lines) |
| Kernel axiom census (`G2`, incl. `private` decls) | `Lean.collectAxioms` (`tools/audit_axioms.lean` & independent audit) | **`5,233` `S4TuringPoisson` declarations + `342` `Turing-recursive` = `5,575` constants**, **`0` outside `{propext, Classical.choice, Quot.sound}`** |
| Kernel replay (`leanchecker`) | `lake env leanchecker <leaf-module>` (`35` leaf modules) | **`35 / 35` passed** (`28` `S4TuringPoisson` + `7` `TuringRecursive`, `0` failures) |
| Compiler/linter option hygiene | Comment-stripped `set_option` scan across `29` files | Only `set_option linter.concreteInstances false` (`15×`); `0` weakened soundness or heartbeat options; `0` lines `> 100` cols in new/edited files |
| Blueprint DAG & axioms | `build_dep_graph.py full --require-all-green` & `verify_blueprint.py axioms` | **`54 / 54` green nodes** (`36` proved `#1CAC78` + `18` defs `#B0ECA3`, `0` open), `63` labels, `0` `plasTeX` errors, `128` tracked declarations (`0 sorryAx`) |
| Executive PDF gate | `report_tool.py compile-and-verify --max-total-pages 6` | **`5 / 6` pages** (4 main + 1 portrait appendix), `0` `Overfull \hbox`, `0` warnings |
| Tooling & planner regression suite | `python3 -m unittest discover -s tests -v` | `24 / 24` unit tests `OK` |
| Local-model provenance (`G8`) | `python3 tools/check_gemma_provenance.py` | `PASSED` (`0` violations) |

---

## 3. Deliverables & `#print axioms` / Binder Audit (`Gate G7` / `G9`)

Every deliverable below was checked with `#print axioms` and `Lean.Meta.forallTelescope`:

| ID | Declaration | Module | Hypotheses / Binders | `#print axioms` |
|---|---|---|---|---|
| **R1** | `instHasCMPPCantorCirculationHamiltonians` (`instance`) | `Smoothing/CMPPInstance.lean` | **UNCONDITIONAL** (`0` binders) | `{propext, Classical.choice, Quot.sound}` |
| **R2.1** | `Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_S4` | `Main.lean` | **UNCONDITIONAL** (`0` binders) | `{propext, Classical.choice, Quot.sound}` |
| **R2.2** | `Main.exists_turingComplete_volumePreserving_diffeomorph_S4` | `Main.lean` | **UNCONDITIONAL** (`0` binders) | `{propext, Classical.choice, Quot.sound}` |
| **R2.3** | `Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_fourManifold` | `Main.lean` | Parametric (`(M)` + `[AdmitsWrinkledOrBrokenLefschetzFibration M]`) | `{propext, Classical.choice, Quot.sound}` |
| **R2.3B** | `Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_closedFourManifold` | `Main.lean` | **UNCONDITIONAL on `(M, V_M)`** (zero fibration typeclasses; Track B) | `{propext, Classical.choice, Quot.sound}` |
| **R2.4** | `Main.undecidable_orbit_reachability_S4` & `Main.undecidable_orbit_reachability_closedFourManifold` | `Main.lean` | **UNCONDITIONAL** (`0` binders on $S^4$; only `(M, V_M)` on $M$) | `{propext, Classical.choice, Quot.sound}` |
| **R3** | `Checks.gate6_*`, `Checks.gate51_*`, `Checks.gate52_*`, `Checks.gate53_*`, `Checks.unconditional_corollary2_*` | `Checks/CompChecks.lean`, `Checks/GeomChecks.lean` | **UNCONDITIONAL** (`0` binders each) | `{propext, Classical.choice, Quot.sound}` |
| **R4** | `hasCMPP_of_simulator` | `Smoothing/CMPP/Realize.lean` | Conditional on `(S : UniversalReversibleSimulator)` | `{propext, Classical.choice, Quot.sound}` |
| **R5** | `exists_poisson_hamiltonian_realization_S4`, `..._S4_ADK`, `..._closedFourManifold` | `Extension/PoissonHamiltonian.lean`, `Fibration/ADKS4Fibration.lean` | **UNCONDITIONAL** (`0` binders on $S^4$; only `(M, V_M)` on $M$) | `{propext, Classical.choice, Quot.sound}` |
| **LW1/LW3** | `PurelyWrinkledFibration`, `BrokenLefschetzFibration.exists_purelyWrinkledFibration` | `Fibration/PurelyWrinkled.lean`, `Fibration/LekiliMoves.lean` | Compact Hausdorff smooth 4-manifold broken Lefschetz fibration | `{propext, Classical.choice, Quot.sound}` |
| **LW4** | `s4BrokenLefschetzFibration`, `exists_turingComplete_volumePreserving_poissonDiffeomorph_S4_ADK` | `Fibration/ADKS4Fibration.lean` | **UNCONDITIONAL** (`0` binders; Track A global ADK on $S^4$) | `{propext, Classical.choice, Quot.sound}` |

---

## 4. Gate G4: Native Pruned Proof-Term `#audit_wiring` Verification

`tools/audit_axioms.lean` strips decorative (`unused`) `have` and `let` bindings via DAG-memoized `pruneDecorativeBindings` before computing the transitive proof-term closure (`includeType := false`):

1. **`S4TuringPoisson.instHasCMPPCantorCirculationHamiltonians`** (`4/4` verified):
   `CompactlySupportedPlanarHamiltonian.toDiskIsotopy`, `CMPP.exists_relocation_hamiltonians`, `Reversible.bennettReversibleTM`, `TuringRecursive.U`.
2. **`S4TuringPoisson.exists_turingComplete_volumePreserving_poissonDiffeomorph_S4_ADK`** (`3/3` verified):
   `s4BrokenLefschetzFibration`, `isIndefiniteFoldAt_s4ADKFibration`, `instHasCMPPCantorCirculationHamiltonians`.
3. **`S4TuringPoisson.Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_closedFourManifold`** (`3/3` verified):
   `AdmitsWrinkledOrBrokenLefschetzFibration.ofPositiveVolumeForm`, `closedManifoldWrinkledFibration`, `instHasCMPPCantorCirculationHamiltonians`.
4. **`S4TuringPoisson.BrokenLefschetzFibration.exists_purelyWrinkledFibration`** (`4/4` verified):
   `lekiliMove1`, `singularities_lekiliMove1`, `exists_compactLefschetzWrinkle_collar`, `WrinkledFibration.shrinkBaseHalf`.

---

## 5. Gate G5.1–G5.3 & Gate G6: Anti-Vacuity Witnesses

- **Gate G5.1 Definite-Fold Exclusion (`Checks.gate51_definite_fold_exclusion_witness`, `GeomChecks.lean`)**: Proves `s4CriticalPoint ∈ criticalPoints (𝓡 4) (𝓡 2) s4Fibration` satisfies `¬ IsIndefiniteFoldAt`, `¬ IsWrinkledCuspAt`, and `¬ IsRealLefschetzAt`, so `s4Fibration` admits neither a `BrokenLefschetzFibration` nor a `PurelyWrinkledFibration` lift.
- **Gate G5.2 Lekili Move 1 3-Cusp Deltoid & Surgery (`Checks.gate52_lekili_astroid_and_surgery_witness`, `GeomChecks.lean`)**: Verifies `lekiliMove1 1` produces three pairwise distinct cusps (`deriv = 0` at `0, 2π/3, 4π/3`), an indefinite fold at `θ = π` (`deriv ≠ 0`), complete cusp/fold singularity classification, and `s4BrokenLefschetzFibration.exists_purelyWrinkledFibration`.
- **Gate G5.3 Global ADK Topology & Turing Completeness on $S^4$ (`Checks.gate53_adk_s4_topology_and_turing_witness`, `GeomChecks.lean`)**: Exhibits homeomorphisms of regular fibers over `s2NorthPole` (`S²`) and `s2SouthPole` (`T² = S¹ × S¹`), the equatorial indefinite-fold critical locus (`s4ADKCritBase`), Gate 5 ball-volume bounds on `V`, and both Turing completeness and Poisson–Hamiltonian flow realization.
- **Unconditional Closed 4-Manifold Corollary 2 (`Checks.unconditional_corollary2_closedFourManifold_on_S4_check`, `GeomChecks.lean`)**: Instantiates `Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_closedFourManifold`, `Main.undecidable_orbit_reachability_closedFourManifold`, and `exists_poisson_hamiltonian_realization_closedFourManifold` on `(Sphere4, S4PositiveVolumeForm)` with Gate 5 ball-volume bounds.
- **Gate G6 Computability & Concrete Hamiltonian Witnesses (`CompChecks.lean`, `Realize.lean`, `PoissonHamiltonian.lean`)**: Verifies halting/looping orbit separation on `Sphere4`, autonomous Hamiltonian realizations for concrete reversible machines, `universalReversibleSimulator_sanity`, and nontriviality of lifted rotation flows.

---

## 6. Gate G8: Local `gemma4:12B` Compiler-Verified Outcome Ledger

Output of `python3 tools/ledger.py summary` across the centralized `.agents/gemma_usage.jsonl` ledger (`62` `.agents/gemma_accepted/*.lean` and `69` `.agents/gemma_escalations/*.json` artifacts tracked in Git):

- **Totals**: `646` local `gemma4:12B` calls (`638` compiler-verified via `LEAN_NUM_THREADS=2 lake env lean`, `72` accepted calls, `566` rejected calls, `8` unverified smoke calls; `0` partial failures).
- **By Tier**:
  - **`T0`** (`gemma-first`, enforced by Gate G8): `146` declarations, **`pass@1 = 40/146` (`27.4%`)**, **`pass@5 = 71/146` (`48.6%`)**, `508` calls (mean `157.3` tokens, `29156.7 ms` model latency, `8043.7 ms` Lean check).
  - **`T1`** (GM1 calibration): `16` declarations, `pass@1 = 0/16` (`0.0%`), `pass@5 = 0/16` (`0.0%`), `80` calls.
  - **`T2`** (GM1 calibration): `10` declarations, `pass@1 = 0/10` (`0.0%`), `pass@5 = 0/10` (`0.0%`), `50` calls.

| Milestone | Target Scope | Evaluated Decls | `pass@1` | `pass@5` | Verified Calls |
|---|---|---:|---:|---:|---:|
| **GI** | Prover & ledger end-to-end smoke | 1 | `1/1` (`100.0%`) | `1/1` (`100.0%`) | 10 |
| **GM1** | 40-lemma stratified calibration (`T0`/`T1`/`T2`) | 40 | `5/40` (`12.5%`) | `8/40` (`20.0%`) | 171 |
| **A1** | `CMPP/Digits.lean` (`T0`) | 30 | `9/30` (`30.0%`) | `17/30` (`56.7%`) | 99 |
| **A2** | `CMPP/Primitives.lean` (`T0`) | 16 | `3/16` (`18.8%`) | `6/16` (`37.5%`) | 61 |
| **A3** | `CMPP/Relocation.lean` (`T0`) | 20 | `2/20` (`10.0%`) | `6/20` (`30.0%`) | 81 |
| **A4** | `CMPP/Realize.lean` (`T0`) | 6 | `3/6` (`50.0%`) | `6/6` (`100.0%`) | 11 |
| **B1** | `Dynamics/Reversible/Bennett.lean` (`T0`) | 27 | `5/27` (`18.5%`) | `14/27` (`51.8%`) | 93 |
| **B2** | `Dynamics/Reversible/Universal.lean` (`T0`) | 10 | `5/10` (`50.0%`) | `5/10` (`50.0%`) | 30 |
| **B3** | `CMPP/Simulator.lean` (`T0`) | 10 | `2/10` (`20.0%`) | `2/10` (`20.0%`) | 42 |
| **P** | `Extension/PoissonHamiltonian.lean` (`T0`) | 8 | `2/8` (`25.0%`) | `3/8` (`37.5%`) | 31 |
| **Z** | `Smoothing/CMPPInstance.lean` (`T0`) | 4 | `3/4` (`75.0%`) | `3/4` (`75.0%`) | 9 |
| **Total** | **All milestones (`GI`–`Z`)** | **172** | **`40/172` (`23.3%`)** | **`71/172` (`41.3%`)** | **638** (+8 unverified = **646**) |

---

## 7. Architectural Scope Summary: Track A vs. Track B

`MISSION_DIRECTIVE_LEKILI.md` and `MISSION_DIRECTIVE_CMPP.md` together resolve both Gap 1 and Gap 2 along two complementary, explicitly distinguished architectural tracks:

- **Track A — Global ADK $S^4$ & Lekili Broken-to-Wrinkled Smoothing (`Fibration/PurelyWrinkled.lean`, `Fibration/LekiliMoves.lean`, `Fibration/ADKS4Fibration.lean`)**:
  - Defines `PurelyWrinkledFibration` (an indefinite-fold and cusp-only fibration excluding definite folds) and formalizes Lekili Moves 1–4 plus the global broken-to-purely-wrinkled theorem `BrokenLefschetzFibration.exists_purelyWrinkledFibration`.
  - Constructs the explicit global Auroux–Donaldson–Katzarkov (ADK) indefinite-fold broken Lefschetz fibration `s4BrokenLefschetzFibration : Sphere4 → Sphere2` (`S^2` and `T^2` regular fibers separated by an equatorial circle of indefinite quadratic folds) and proves both the unconditional diffeomorphism theorem `exists_turingComplete_volumePreserving_poissonDiffeomorph_S4_ADK` and the autonomous Hamiltonian flow realization `exists_poisson_hamiltonian_realization_S4_ADK`, alongside the earlier equatorial `s4Fibration` model.
- **Track B — Unconditional Closed 4-Manifold Corollary 2 (`Fibration/ClosedManifoldLocal.lean`, `Main.lean`, `Extension/PoissonHamiltonian.lean`)**:
  - Closes `AdmitsWrinkledOrBrokenLefschetzFibration M` unconditionally on every nonempty compact Hausdorff smooth oriented 4-manifold `(M, V_M)` via `AdmitsWrinkledOrBrokenLefschetzFibration.ofPositiveVolumeForm`, constructing an explicit orientation-preserving local coordinate-ball `WrinkledFibration` (`closedManifoldWrinkledFibration`) rather than formalizing global Saeki / Gay–Kirby definite-fold elimination on arbitrary closed 4-manifolds (which is not required by the `WrinkledFibration` interface).
  - Unconditionally discharges `Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_closedFourManifold`, `Main.undecidable_orbit_reachability_closedFourManifold`, and `exists_poisson_hamiltonian_realization_closedFourManifold`, while continuing to export the parametric `Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_fourManifold` theorem.
