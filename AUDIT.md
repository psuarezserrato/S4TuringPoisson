# Audit of the `S4TuringPoisson` Formalization (Sound & Complete: `S1`–`S6` Closed)

Repository: `S4TuringPoisson` (Lean `v4.36.0`, Mathlib `fc4f59e5` + `TauCeti` `d91980bdc` + `Turing-recursive` `4120346`).
Supersedes the `bc772ad` semantic re-audit upon completion of `MISSION_DIRECTIVE_SOUND_AND_COMPLETE.md` (`SC1`–`SC4` & `SC-Final`), closing all six semantic findings (`S1`–`S6`) and all four recommendations (`(i)`–`(iv)`).

## 1. Verdict
- **Sound and Complete**: **yes**. All `10,266` Lake build jobs pass with `--wfail`, zero forbidden tokens exist across all `30` `.lean` files (`51,058` lines), `36/36` leaf modules (`29` `S4TuringPoisson.*` + `7` `TuringRecursive.*`) pass `leanchecker` kernel replay, and `Lean.collectAxioms` over all `6,124` `S4TuringPoisson` declarations (plus `342` `Turing-recursive` declarations = `6,466` total) reports strictly `{propext, Classical.choice, Quot.sound}`. Every exported docstring, interface, and theorem statement matches its proved conclusion (`0` open semantic caveats).
- **Headline Theorems & Unconditional Status**:
  - **$S^4$ (Definite-Fold Projection & Exact Round Volume)**: Unconditional (`0` binders) for `Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_S4`, `Main.exists_turingComplete_exactVolumePreserving_poissonDiffeomorph_S4` (preserving `S4PositiveVolumeForm.Ω` identically), `Main.undecidable_orbit_reachability_S4`, `exists_poisson_hamiltonian_realization_S4`, and `exists_exactVolumePreserving_poisson_hamiltonian_realization_S4` (`R5`, with `IsGenericallyRankTwo`).
  - **$S^4$ (Global ADK Broken Lefschetz Fibration — Track A)**: Unconditional (`0` binders) for `exists_turingComplete_volumePreserving_poissonDiffeomorph_S4_ADK`, `Main.exists_turingComplete_exactVolumePreserving_poissonDiffeomorph_S4_ADK`, `undecidable_orbit_reachability_S4_ADK`, and `exists_exactVolumePreserving_poisson_hamiltonian_realization_S4_ADK`, with smooth $C^\infty$ fiber diffeomorphisms (`s4ADKNorthFiberDiffeomorph` $\simeq_m S^2$, `s4ADKTorusFiberDiffeomorph` $\simeq_m T^2$) and two-sided trivializations (`s4BrokenLefschetzFibration`, `s4ADKTorusBrokenLefschetzFibration`).
  - **Lekili Moves 1–4 & Compactly Supported Broken-to-Wrinkled Homotopy (`SC2` — Track A)**: Closed-form fold/cusp normal forms for all four local $\mathbb{R}^4 \to \mathbb{R}^2$ families (`lekiliMove1`–`lekiliMove4`), chiral vs. achiral Lefschetz classification (`IsChiralRealLefschetzAt`), and global compactly supported smooth homotopy `BrokenLefschetzFibration.exists_purelyWrinkledFibration` (`Lekili 2009`, §3.1 & §4 / Theorem 4).
  - **Track A Generically Rank-2 Corollary 2 (`SC3` & `SC4`, Rec `(iv)`)**: Over any positively co-oriented `PurelyWrinkledFibration` or `BrokenLefschetzFibration` (`Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_of_purelyWrinkled`, `..._of_brokenLefschetz`, and exact-`V_M` Moser conjugates), exporting `π_f.IsGenericallyRankTwo` (open dense rank-2 locus).
  - **Literal Unconditional Closed 4-Manifold Corollary 2 (`SC4` — Track B + Moser)**: Unconditional on any nonempty compact Hausdorff smooth 4-manifold `(M, V_M)` (`Main.exists_turingComplete_exactVolumePreserving_diffeomorph_closedFourManifold`, `Main.exists_turingComplete_exactVolumePreserving_poissonDiffeomorph_closedFourManifold`, `Main.undecidable_orbit_reachability_exactVolumePreserving_closedFourManifold`, and `exists_exactVolumePreserving_poisson_hamiltonian_realization_closedFourManifold`), requiring **zero** `[ConnectedSpace M]` or fibration typeclasses and preserving **`V_M.Ω` and `V_M.μ` identically**.

---

## 2. Kernel, Build & Static Verification Summary

| Check | Command | Observed Result |
|---|---|---|
| Full workspace build (`G1`) | `LEAN_NUM_THREADS=2 lake build --wfail` | `10,266 / 10,266` jobs succeeded, `0` errors, `0` warnings |
| Comment-stripped forbidden-token scan (`G2`) | `LEAN_NUM_THREADS=2 bash tools/collect_axioms.sh` | `0` occurrences of `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `native_decide`, `opaque`, `maxHeartbeats` across `30` `.lean` files (`51,058` lines) |
| Kernel axiom census (`G2`, incl. `private` decls) | `Lean.collectAxioms` (`tools/audit_axioms.lean` & independent audit) | **`6,124` `S4TuringPoisson` declarations + `342` `Turing-recursive` = `6,466` constants**, **`0` outside `{propext, Classical.choice, Quot.sound}`** |
| Kernel replay (`leanchecker`) | `lake env leanchecker <leaf-module>` (`36` leaf modules) | **`36 / 36` passed** (`29` `S4TuringPoisson` + `7` `TuringRecursive`, `0` failures) |
| Compiler/linter & formatting hygiene (`G1`) | Comment-stripped `set_option` + header + column scan across `30` files | Only `set_option linter.concreteInstances false` (`16×`); 9-line AGPLv3 header on `30/30` files; `0` lines `> 100` cols across all `51,058` lines |
| Blueprint DAG & axioms (`G9`) | `build_dep_graph.py full --require-all-green` & `verify_blueprint.py axioms` | **`56 / 56` green nodes** (`38` proved `#1CAC78` + `18` defs `#B0ECA3`, `0` open), `65` labels, `0` `plasTeX` errors, `163` tracked declarations (`0 sorryAx`) |
| Executive PDF gate (`G10`) | `report_tool.py compile-and-verify --max-total-pages 6` | **`5 / 6` pages** (4 main + 1 portrait appendix), `0` `Overfull \hbox`, `0` warnings |
| Tooling & planner regression suite (`G6`) | `python3 -m unittest discover -s tests -v` | `24 / 24` unit tests `OK` |
| Local-model provenance (`G8`) | `python3 tools/check_gemma_provenance.py` | `PASSED` (`0` violations) |

---

## 3. Resolution of Semantic Findings `S1`–`S6` & Recommendations `(i)`–`(iv)`

| ID | Original Finding (`bc772ad`) | Verified Resolution (`SC1`–`SC4`) |
|---|---|---|
| **S1** + **Rec (i), (iv)** | Track B map `closedManifoldLocalMap` is constant outside one coordinate ball (`¬ Dense` rank-2 locus); `Main.lean` docstring overstated `"generically rank-2"`; no `PurelyWrinkledFibration` Corollary 2 exported rank-2 density. | Corrected `Main.lean` docstring; defined `PoissonStructure.IsGenericallyRankTwo` (`IsOpen` $\wedge$ `Dense` rank-2 locus); proved it for every `[AdmitsWrinkledOrBrokenLefschetzFibration M]` and exported `exists_turingComplete_volumePreserving_poissonDiffeomorph_of_purelyWrinkled` & `..._of_brokenLefschetz` (plus exact-`V_M` Moser conjugates); proved `not_isGenericallyRankTwo_closedManifoldLocal`. |
| **S2** | `WrinkledFibration` imposed no singularity normal forms, making `AdmitsWrinkledOrBrokenLefschetzFibration` wrinkled in name only. | Removed `WrinkledFibration` repo-wide (`0` unconstrained `*WrinkledFibration*` names; renamed to `RegularDiskFibration` / `AdmitsRegularDiskFibration M`); upgraded `AdmitsWrinkledOrBrokenLefschetzFibration M` to enforce `IsIndefiniteFoldAt ∨ IsWrinkledCuspAt ∨ IsRealLefschetzAt` at every critical point. |
| **S3** + **Rec (ii)** | `encodeOpen` was unconstrained in `TuringCompleteWitness` (permitting non-effective targets and periodic twist-rotation counterexamples). | Added `RatBox2`, open-tube `openChart : Param × UnitDisk2 → X` (`IsOpenEmbedding`), `computable_encodeOpen` (`Computable enumBoxes`), and `orbit_encodePoint_injective` (`IsTuringComplete.iterate_ne_id : ∀ p > 0, φ^[p] ≠ id`); exported `Computable targetBoxes` in all undecidability theorems and proved `Checks.periodic_rotation_not_isTuringComplete`. |
| **S4** + **Rec (i), (iii)** | `BrokenLefschetzFibration.exists_purelyWrinkledFibration` kept surgery locality and smooth homotopy proof-internal and cited `"Theorem 1.1"`. | Exported compact surgery support `K : Set M` (disjoint from `B.toFun ⁻¹' closure P.baseRegion.1` and from all non-Lefschetz critical points, with `P.toFun = B.toFun` outside `K`) and jointly $C^\infty$ global homotopy `H : ℝ → M → Base`; updated citation to Lekili (2009) §3.1 & §4 / Theorem 4. |
| **S5** + **Rec (i)** | `LekiliMoves.lean` header overstated Move 4 charts (`criticalPoints` only) and Moves 2–4 were unused externally. | Proved `isIndefiniteFoldAt_lekiliMove4`, `isWrinkledCuspAt_lekiliMove4`, `singularities_lekiliMove4_pos`, and `singularities_lekiliMove4_neg`; updated `LekiliMoves.lean` header; added `Checks.gate54_lekili_moves_234_witness`. |
| **S6** | ADK fibers were `Homeomorph`s with north-only trivialization; `V` was proportional to `V_M`; `V.μ` was unpinned; `IsRealLefschetzAt` lacked a chiral companion. | Upgraded ADK fibers to $C^\infty$ `Diffeomorph`s (`s4ADKNorthFiberDiffeomorph`, `s4ADKTorusFiberDiffeomorph`) and added south trivialization `s4ADKTorusBrokenLefschetzFibration`; proved componentwise Moser conjugation (`Extension/MoserVolume.lean`) preserving `V_M.Ω` and `V_M.μ` identically; pinned `V.μ = RoughForm.measure V.Ω.1` across all 21 public existential theorems; defined `IsChiralRealLefschetzAt` and proved achiral separation. |

---

## 4. Deliverables & `#print axioms` / Binder Audit (`Gate G7` / `G9`)

Every deliverable below was checked with `#print axioms` and `Lean.Meta.forallTelescope` (`14` zero-binder $S^4$ declarations verified):

| ID | Declaration | Module | Hypotheses / Binders | `#print axioms` |
|---|---|---|---|---|
| **R1** | `instHasCMPPCantorCirculationHamiltonians` (`instance`) | `Smoothing/CMPPInstance.lean` | **UNCONDITIONAL** (`0` binders) | `{propext, Classical.choice, Quot.sound}` |
| **R2.1 / SC4** | `Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_S4`, `Main.exists_turingComplete_exactVolumePreserving_poissonDiffeomorph_S4` | `Main.lean` | **UNCONDITIONAL** (`0` binders; aligned & exact round $\Omega_{S^4}$) | `{propext, Classical.choice, Quot.sound}` |
| **R2.2 / SC4** | `Main.exists_turingComplete_volumePreserving_diffeomorph_S4`, `Main.exists_turingComplete_exactVolumePreserving_diffeomorph_S4` | `Main.lean` | **UNCONDITIONAL** (`0` binders) | `{propext, Classical.choice, Quot.sound}` |
| **R2.3 / SC3** | `Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_fourManifold`, `..._of_purelyWrinkled`, `..._of_brokenLefschetz` | `Main.lean` | Singularity-enforced (`[AdmitsWrinkledOrBrokenLefschetzFibration M]` / `PurelyWrinkledFibration` / `BrokenLefschetzFibration`; exports `IsGenericallyRankTwo`) | `{propext, Classical.choice, Quot.sound}` |
| **R2.3B / SC4** | `Main.exists_turingComplete_exactVolumePreserving_diffeomorph_closedFourManifold`, `..._poissonDiffeomorph_closedFourManifold` | `Main.lean`, `Extension/MoserVolume.lean` | **UNCONDITIONAL on `(M, V_M)`** (zero fibration or connectedness assumptions; exact `V_M.Ω` & `V_M.μ`) | `{propext, Classical.choice, Quot.sound}` |
| **R2.4 / SC1** | `Main.undecidable_orbit_reachability_S4`, `..._S4_ADK`, `..._of_purelyWrinkled`, `..._exactVolumePreserving_closedFourManifold` | `Main.lean`, `Fibration/ADKS4Fibration.lean` | **UNCONDITIONAL** (`0` binders on $S^4$; only `(M, V_M)` on $M$; exports `Computable targetBoxes`) | `{propext, Classical.choice, Quot.sound}` |
| **R3 / SC1–4** | `Checks.gate51_*`–`Checks.gate54_*`, `Checks.gate6_*`, `Checks.periodic_rotation_not_isTuringComplete`, `Checks.closedManifoldLocal_not_genericallyRankTwo`, `Checks.exact_moser_volume_*` | `Checks/CompChecks.lean`, `Checks/GeomChecks.lean` | **UNCONDITIONAL** (`0` binders each) | `{propext, Classical.choice, Quot.sound}` |
| **R5 / SC4** | `exists_poisson_hamiltonian_realization_S4`, `exists_exactVolumePreserving_poisson_hamiltonian_realization_S4`, `..._S4_ADK`, `..._closedFourManifold` | `Extension/PoissonHamiltonian.lean`, `Extension/MoserVolume.lean` | **UNCONDITIONAL** (`0` binders on $S^4$; only `(M, V_M)` on $M$) | `{propext, Classical.choice, Quot.sound}` |
| **LW1/LW3/SC2** | `PurelyWrinkledFibration`, `BrokenLefschetzFibration.exists_purelyWrinkledFibration` | `Fibration/PurelyWrinkled.lean`, `Fibration/LekiliMoves.lean` | Compact Hausdorff smooth 4-manifold broken Lefschetz fibration (exports compact `K` & smooth homotopy `H`) | `{propext, Classical.choice, Quot.sound}` |
| **LW4 / SC3** | `s4BrokenLefschetzFibration`, `s4ADKTorusBrokenLefschetzFibration`, `s4ADKNorthFiberDiffeomorph`, `s4ADKTorusFiberDiffeomorph`, `exists_turingComplete_volumePreserving_poissonDiffeomorph_S4_ADK` | `Fibration/ADKS4Fibration.lean` | **UNCONDITIONAL** (`0` binders; smooth $S^2$ & $T^2$ fibers) | `{propext, Classical.choice, Quot.sound}` |

---

## 5. Gate G4: Native Pruned Proof-Term `#audit_wiring` Verification

`tools/audit_axioms.lean` strips decorative (`unused`) `have` and `let` bindings via DAG-memoized `pruneDecorativeBindings` before computing the transitive proof-term closure (`includeType := false`), verifying `6/6` chains (`24` dependencies):

1. **`S4TuringPoisson.instHasCMPPCantorCirculationHamiltonians`** (`4/4` verified):
   `CompactlySupportedPlanarHamiltonian.toDiskIsotopy`, `CMPP.exists_relocation_hamiltonians`, `Reversible.bennettReversibleTM`, `TuringRecursive.U`.
2. **`S4TuringPoisson.exists_turingComplete_volumePreserving_poissonDiffeomorph_S4_ADK`** (`4/4` verified):
   `s4BrokenLefschetzFibration`, `isIndefiniteFoldAt_s4ADKFibration`, `isGenericallyRankTwo_adaptedJacobianPoisson`, `instHasCMPPCantorCirculationHamiltonians`.
3. **`S4TuringPoisson.Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_closedFourManifold`** (`3/3` verified):
   `AdmitsRegularDiskFibration.ofPositiveVolumeForm`, `closedManifoldRegularDiskFibration`, `instHasCMPPCantorCirculationHamiltonians`.
4. **`S4TuringPoisson.BrokenLefschetzFibration.exists_purelyWrinkledFibration`** (`4/4` verified):
   `lekiliMove1`, `singularities_lekiliMove1`, `exists_compactLefschetzWrinkle_collar`, `RegularDiskFibration.shrinkBaseHalf`.
5. **`S4TuringPoisson.Main.exists_turingComplete_exactVolumePreserving_diffeomorph_closedFourManifold`** (`5/5` verified):
   `TauCeti.mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero`, `TauCeti.compactlySupportedDeRhamCohomology.bijective_integral`, `MoserVolume.ofPositivelyCooriented`, `instHasCMPPCantorCirculationHamiltonians`, `TuringRecursive.U`.
6. **`S4TuringPoisson.Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_of_purelyWrinkled`** (`4/4` verified):
   `AdmitsWrinkledOrBrokenLefschetzFibration.ofPurelyWrinkled`, `isGenericallyRankTwo_adaptedJacobianPoisson`, `dense_regularPoints_of_wrinkled_or_lefschetz`, `instHasCMPPCantorCirculationHamiltonians`.

---

## 6. Gate G5.1–G5.4 & Gate G6: Adversarial Anti-Vacuity & Refutation Witnesses

- **Gate G5.1 Definite-Fold Exclusion (`Checks.gate51_definite_fold_exclusion_witness`, `GeomChecks.lean`)**: Proves `s4CriticalPoint ∈ criticalPoints (𝓡 4) (𝓡 2) s4Fibration` satisfies `¬ IsIndefiniteFoldAt`, `¬ IsWrinkledCuspAt`, and `¬ IsRealLefschetzAt`, so `s4Fibration` lifts neither to `BrokenLefschetzFibration` nor to `PurelyWrinkledFibration`.
- **Gate G5.2 Lekili Move 1 3-Cusp Deltoid & Compactly Supported Homotopy (`Checks.gate52_lekili_astroid_and_surgery_witness`, `GeomChecks.lean`)**: Verifies `lekiliMove1 1` produces three pairwise distinct cusps (`0, 2π/3, 4π/3`), an indefinite fold at `θ = π`, complete cusp/fold classification, and compactly supported homotopy on `s4BrokenLefschetzFibration`.
- **Gate G5.3 Global ADK Smooth Fibers & Two-Sided Trivialization (`Checks.gate53_adk_s4_topology_and_turing_witness`, `GeomChecks.lean`)**: Verifies smooth $C^\infty$ `Diffeomorph`s of regular fibers over `s2NorthPole` ($S^2$) and `s2SouthPole` ($T^2 = S^1 \times S^1$), two-sided trivializations, `IsGenericallyRankTwo`, and Turing completeness.
- **Gate G5.4 Lekili Moves 2–4 & Chiral/Achiral Separation (`Checks.gate54_lekili_moves_234_witness`, `GeomChecks.lean`)**: Verifies 2-cusp birth (`lekiliMove2 1`), cusp-merge (`lekiliMove3`), swallowtail flip (`lekiliMove4 1` fold-only vs. `lekiliMove4 (-3)` 2-cusp + fold classification), and `achiralRealLefschetzMap` (`IsRealLefschetzAt` $\wedge$ `¬ IsChiralRealLefschetzAt`).
- **Track B Separation & Exact Moser Volume (`Checks.closedManifoldLocal_not_genericallyRankTwo`, `Checks.exact_moser_volume_S4_and_closedFourManifold_witness`, `GeomChecks.lean`)**: Proves Track B's coordinate-ball map on `Sphere4` has nonempty critical interior (`¬ IsGenericallyRankTwo`, cannot inhabit `AdmitsWrinkledOrBrokenLefschetzFibration`), and verifies `d_exact^* S4PositiveVolumeForm.Ω = S4PositiveVolumeForm.Ω` plus R5 Hamiltonian realization.
- **Gate G6 Computability, Rational Target Boxes & Periodic Refutation (`CompChecks.lean`)**: Proves `Checks.periodic_rotation_not_isTuringComplete` (refuting period-2 disk rotation `(x, y) ↦ (-x, -y)`), exhibits positive-measure computable rational target boxes (`Checks.sphere4_undecidable_targetBoxes_witness`), and verifies halting/looping orbit separation on `Sphere4`.

---

## 7. Gate G8: Local `gemma4:12B` Compiler-Verified Outcome Ledger

Output of `python3 tools/ledger.py summary` across the centralized `.agents/gemma_usage.jsonl` ledger (`65` `.agents/gemma_accepted/*.lean` and `70` `.agents/gemma_escalations/*.json` artifacts tracked in Git):

- **Totals**: `674` local `gemma4:12B` calls (`666` compiler-verified via `LEAN_NUM_THREADS=2 lake env lean`, `75` accepted calls, `591` rejected calls, `8` unverified smoke calls; `0` partial failures).
- **By Tier**:
  - **`T0`** (`gemma-first`, enforced by Gate G8): `150` declarations, **`pass@1 = 42/150` (`28.0%`)**, **`pass@5 = 74/150` (`49.3%`)**, `536` calls (mean `158.1` tokens, `29470.5 ms` model latency, `8126.2 ms` Lean check).
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
| **SC1** | `Interfaces` & `RatBox2` / `Simulator` (`T0`) | 4 | `2/4` (`50.0%`) | `3/4` (`75.0%`) | 28 |
| **Total** | **All milestones (`GI`–`SC1`)** | **176** | **`42/176` (`23.9%`)** | **`74/176` (`42.0%`)** | **666** (+8 unverified = **674**) |

---

## 8. Architectural Scope Summary: Track A, Track B & Moser Exact Volume

- **Track A — Singularity-Enforced Fibrations, Global ADK $S^4$, Lekili Homotopy & Generic Rank 2**:
  - `AdmitsWrinkledOrBrokenLefschetzFibration M` enforces that every critical point on $M$ is an indefinite fold, wrinkled cusp, or real Lefschetz point, which implies `IsGenericallyRankTwo` (open dense rank-2 locus) for `adaptedJacobianPoisson`.
  - On $S^4$, `s4BrokenLefschetzFibration` (`ADK05`) provides an unconditional global inhabitant with smooth $S^2$ and $T^2$ fibers and two-sided trivializations. On general closed 4-manifolds, `Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_of_purelyWrinkled` and `..._of_brokenLefschetz` (plus their exact-`V_M` Moser conjugates) formalize the complete generically rank-2 Corollary 2 modulo only Gay–Kirby's 4-manifold handlebody existence theorem (`GK07`).
- **Track B + Componentwise Moser Conjugation — Literal Unconditional Corollary 2 on `(M, V_M)`**:
  - `AdmitsRegularDiskFibration.ofPositiveVolumeForm` constructs a smooth coordinate-ball `RegularDiskFibration` on any nonempty compact Hausdorff smooth 4-manifold `(M, V_M)` (explicitly distinguished from Track A via `not_isGenericallyRankTwo_closedManifoldLocal`).
  - `MoserVolume.ofPositivelyCooriented` (`Extension/MoserVolume.lean`) applies `TauCeti`'s top-degree de Rham integration isomorphism and Moser's trick on each clopen connected component (requiring **zero** `[ConnectedSpace M]` assumption), conjugating the leafwise lift and R5 Hamiltonian flows so `d_exact` preserves **`V_M.Ω` and `V_M.μ` identically**.
