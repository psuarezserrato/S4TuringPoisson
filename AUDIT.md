# Audit of the `S4TuringPoisson` Formalization (CMPP Milestone Z / Gate G9)

Repository: `S4TuringPoisson` (Lean `v4.36.0`, Mathlib + `TauCeti` `v4.36.0`).
Supersedes the `main @ c530a68` audit upon completion of `MISSION_DIRECTIVE_CMPP.md` (Milestones C0, GI, GM1, A1–A4, B1–B3, P, Z).

## 1. Verdict
- **Sound**: **yes**. All `9,450` Lake build jobs pass with `--wfail`, zero forbidden tokens exist across all `25` `.lean` files (`30,200` lines), and `Lean.collectAxioms` over all `4,057` declarations (`2,482` non-internal `S4TuringPoisson.*` declarations + `1,575` internal/private helpers) reports strictly `{propext, Classical.choice, Quot.sound}`.
- **CMPP Mission Complete (`MISSION_DIRECTIVE_CMPP.md` §1 R1–R5 & §8 Gates G1–G9)**: **yes**.
- **Gap 1 (Conditional Turing completeness)**: **CLOSED (`UNCONDITIONAL`)**. `HasCMPPCantorCirculationHamiltonians` (and hence `HasTuringCompleteAreaPreservingDiskIsotopy`) is unconditionally inhabited by `S4TuringPoisson.instHasCMPPCantorCirculationHamiltonians` (`S4TuringPoisson/Smoothing/CMPPInstance.lean`), discharging all four `Main.lean` headline theorems, `Checks.gate6_sphere4_witness`, and the `S^4` Poisson–Hamiltonian flow realization `exists_poisson_hamiltonian_realization_S4` with zero external typeclass hypotheses on `Sphere4`.
- **Gap 2 (ADK vs. definite-fold $S^4$ fibration & `WrinkledFibration` generality)**: **Open residual outside `MISSION_DIRECTIVE_CMPP.md` scope** (see §6).

---

## 2. Kernel, Build & Static Verification Summary

| Check | Command | Observed Result |
|---|---|---|
| Full workspace build (`G1`) | `LEAN_NUM_THREADS=2 lake build --wfail` | `9450 / 9450` jobs succeeded, `0` errors, `0` warnings |
| Comment-stripped forbidden-token scan (`G2`) | `LEAN_NUM_THREADS=2 bash tools/collect_axioms.sh` | `0` occurrences of `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `native_decide`, `opaque`, `maxHeartbeats` across all `25` `.lean` files (`30,200` lines) |
| Kernel axiom census (`G2`, incl. `private` decls) | `Lean.collectAxioms` (`tools/audit_axioms.lean`) | **`4,057` declarations audited** (`2,482` non-internal `S4TuringPoisson.*`), **`0` outside `{propext, Classical.choice, Quot.sound}`** |
| Compiler/linter option hygiene | Comment-stripped `set_option` scan across `25` files | Only `set_option linter.concreteInstances false` (`14×`); `0` weakened soundness or heartbeat options |
| Anti-vacuity of `IsTuringComplete` (`G3`) | `Interfaces.lean` + Refactor `I2` (`DiskSmoothing.lean`) | Frozen `IsTuringComplete` / `TuringCompleteWitness` / `HaltsWithWindow` / `cantorDiskEmbed`; `encodePoint` depends only on `(M, t)` with `Computable` `2⁻ᵐ` `RatFrac` approximations; `encodeOpen` depends only on `(M, k, w)` and is unconditionally nonempty |
| Tooling & planner regression suite | `python3 -m unittest discover -s tests -q` | `24 / 24` unit tests `OK` |
| Local-model provenance (`G8`) | `python3 tools/check_gemma_provenance.py main...HEAD` | `PASSED` (`0` violations across enforced `T0` tier) |

---

## 3. Deliverables R1–R5 & `#print axioms` Audit (`Gate G7` / `G9`)

Every deliverable below was checked with `#print axioms` and `Lean.Meta.forallTelescope`:

| ID | Declaration | Module | Hypotheses / Binders | `#print axioms` |
|---|---|---|---|---|
| **R1** | `instHasCMPPCantorCirculationHamiltonians` (`instance`) | `Smoothing/CMPPInstance.lean` | **UNCONDITIONAL** (`0` binders; `isInstance = true`) | `{propext, Classical.choice, Quot.sound}` |
| **R2.1** | `Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_S4` | `Main.lean` | **UNCONDITIONAL** (`0` binders; `s4TuringDiffeomorph` has `0` binders) | `{propext, Classical.choice, Quot.sound}` |
| **R2.2** | `Main.exists_turingComplete_volumePreserving_diffeomorph_S4` | `Main.lean` | **UNCONDITIONAL** (`0` binders) | `{propext, Classical.choice, Quot.sound}` |
| **R2.3** | `Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_fourManifold` | `Main.lean` | **UNCONDITIONAL in dynamics** (only manifold `M` + `[AdmitsWrinkledOrBrokenLefschetzFibration M]`) | `{propext, Classical.choice, Quot.sound}` |
| **R2.4** | `Main.undecidable_orbit_reachability_S4` | `Main.lean` | **UNCONDITIONAL** (`0` binders) | `{propext, Classical.choice, Quot.sound}` |
| **R3** | `Checks.gate6_sphere4_witness`, `Checks.gate6_fourManifold_corollary2_on_S4_unconditional`, `Checks.gate6_poisson_hamiltonian_realization_S4` | `Checks/CompChecks.lean` | **UNCONDITIONAL** (`0` binders each; parametric `*_of_cmpp` retained for G6 regression) | `{propext, Classical.choice, Quot.sound}` |
| **R4** | `hasCMPP_of_simulator` | `Smoothing/CMPP/Realize.lean` | **CONDITIONAL-ON-`UniversalReversibleSimulator`** (`(S : UniversalReversibleSimulator)`) | `{propext, Classical.choice, Quot.sound}` |
| **R5** | `exists_poisson_hamiltonian_realization_S4` | `Extension/PoissonHamiltonian.lean` | **UNCONDITIONAL** (`0` binders; finite composition of autonomous `s4AdaptedPoisson` time-`1` Hamiltonian flows) | `{propext, Classical.choice, Quot.sound}` |

---

## 4. Gate G4: Native Pruned Proof-Term `#audit_wiring` Verification

`tools/audit_axioms.lean` strips decorative (`unused`) `have` and `let` bindings via DAG-memoized `pruneDecorativeBindings` (`StateM (Std.HashMap Expr Expr)`, zero namespace filtering) before computing the transitive proof-term closure (`includeType := false`) and rejecting `sorryAx`. All 6 required native `LEAN_NUM_THREADS=2 bash tools/collect_axioms.sh --wiring` audits passed:

1. **`S4TuringPoisson.instHasCMPPCantorCirculationHamiltonians`** (`12.97s`, `10/10` dependencies verified):
   `CompactlySupportedPlanarHamiltonian.toDiskIsotopy`, `S4TuringPoisson.CMPP.exists_translation_hamiltonian` (L1), `S4TuringPoisson.CMPP.bumpedHyperbolicStretchIsotopy_timeOne_of_mem_rect` (L2), `S4TuringPoisson.CMPP.exists_relocation_hamiltonians` (Sliding Lemma / RT), `S4TuringPoisson.CMPP.imageRect_pairwise_disjoint` (Lemma G0), `S4TuringPoisson.ReversibleTM.bijective_eval`, `S4TuringPoisson.Reversible.bennettReversibleTM`, `S4TuringPoisson.Reversible.universalFinTM0`, `TuringRecursive.U`, `S4TuringPoisson.universalReversibleSimulator`.
2. **`S4TuringPoisson.Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_S4`** (`14.81s`, `4/4` dependencies verified):
   `S4TuringPoisson.instHasCMPPCantorCirculationHamiltonians`, `S4TuringPoisson.universalReversibleSimulator`, `S4TuringPoisson.CMPP.exists_relocation_hamiltonians`, `S4TuringPoisson.leafwiseBumpDiffeomorph`.
3. **`S4TuringPoisson.Main.exists_turingComplete_volumePreserving_diffeomorph_S4`** (`14.27s`, `2/2` dependencies verified):
   `S4TuringPoisson.instHasCMPPCantorCirculationHamiltonians`, `S4TuringPoisson.leafwiseBumpDiffeomorph`.
4. **`S4TuringPoisson.Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_fourManifold`** (`14.76s`, `2/2` dependencies verified):
   `S4TuringPoisson.instHasCMPPCantorCirculationHamiltonians`, `S4TuringPoisson.leafwiseBumpDiffeomorph`.
5. **`S4TuringPoisson.Main.undecidable_orbit_reachability_S4`** (`14.82s`, `2/2` dependencies verified):
   `S4TuringPoisson.instHasCMPPCantorCirculationHamiltonians`, `S4TuringPoisson.undecidable_orbit_reachability_leafwiseBumpDiffeomorph`.
6. **`S4TuringPoisson.exists_poisson_hamiltonian_realization_S4`** (`15.28s`, `4/4` dependencies verified):
   `S4TuringPoisson.poissonHamiltonianTimeOneDiffeomorph_liftPlanarHamiltonian_eq`, `S4TuringPoisson.composePoissonHamiltonianTimeOneFlows`, `S4TuringPoisson.universalReversibleSimulator`, `S4TuringPoisson.CMPP.exists_relocation_hamiltonians`.

---

## 5. Gate G5: Concrete Anti-Vacuity & Satisfiability Witnesses

- **Unconditional `Sphere4` Gate 6 Separation (`Checks.gate6_sphere4_witness` & `Checks.gate6_poisson_hamiltonian_realization_S4`, `CompChecks.lean`)**: Instantiates the unconditional `Sphere4` diffeomorphisms on concrete 2-state `FinTM0` machines `M_halt` and `M_loop`, proving `0 < V.μ U_h.1`, `0 < V.μ U_l.1`, positive-step halting reachability `∃ n, d_bar^[n] p_h ∈ U_h`, all-time non-reachability `∀ n, d_bar^[n] p_l ∉ U_l`, fibration leaf invariance `s4Fibration ∘ d_bar = s4Fibration`, `d_bar ≠ id`, and `Main.s4TuringDiffeomorph = composePoissonHamiltonianTimeOneFlows Sphere4 (universalReversibleSimulator_cmpp.generators.map (liftPlanarHamiltonianTo4Manifold Sphere4))`.
- **Concrete Reversible Shift Realizations (`Checks.R_flipRight_realized_by_autonomous_hamiltonians` in `CompChecks.lean`; `CMPP.biDirToyTM_realized_by_autonomous_hamiltonians` in `Realize.lean`)**: Exhibit explicit non-empty autonomous planar Hamiltonian lists inside `Metric.ball 0 (17/20)` realizing concrete unidirectional and 3-direction (`{-1, 0, +1}`) reversible Turing machines on `cantorDiskEmbed` with `diskTimeOneMap ≠ id`.
- **Universal Simulator End-to-End Sanity (`universalReversibleSimulator_sanity`, `CompChecks.lean`)**: Unconditionally verifies `acceptBlocks` non-emptiness, step-`0` exclusion, `n ≥ 1` cylinder entry on `M_halt`/`w_halt`, `∀ n` cylinder exclusion on `M_loop`/`w_loop`, and Gate 6 on `Sphere4`.
- **Single-Hamiltonian 4D Flow Non-Triviality (`poissonHamiltonianTimeOneDiffeomorph_s4Rotation_ne_refl` & `liftPlanarHamiltonianTo4Manifold_s4Rotation_ne_zero`, `PoissonHamiltonian.lean`)**: Verifies that lifting a concrete autonomous planar rotation Hamiltonian to `Sphere4` produces a non-zero smooth Hamiltonian whose time-`1` `s4AdaptedPoisson` flow is `≠ Diffeomorph.refl`.
- **Geometry Non-Degeneracy (`Checks/GeomChecks.lean`)**: Unchanged and green (`9450/9450` build), witnessing rank-`2` regular locus, nonempty rank-`0` singular circle `Crit` on `Sphere4`, and non-atomic volume bounds `0 < μ(B(p, 1/2)) < μ(univ)`.

---

## 6. Gate G8: Local `gemma4:12B` Compiler-Verified Outcome Ledger

Output of `python3 tools/ledger.py summary` across the centralized `.agents/gemma_usage.jsonl` ledger (`62` `.agents/gemma_accepted/*.lean` and `69` `.agents/gemma_escalations/*.json` artifacts tracked in Git):

- **Totals**: `646` local `gemma4:12B` calls (`638` compiler-verified via `LEAN_NUM_THREADS=2 lake env lean`, `72` accepted calls, `566` rejected calls, `8` unverified smoke calls; `0` partial/unlogged escalations).
- **By Tier**:
  - **`T0`** (`gemma-first`, enforced by Gate G8): `146` declarations, **`pass@1 = 40/146` (`27.4%`)**, **`pass@5 = 71/146` (`48.6%`)**, `508` calls (mean `157.3` tokens, `29,156.7 ms` model latency, `8,043.7 ms` Lean check).
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

## 7. Honest Residual Architectural Note: Gap 2 (Outside `MISSION_DIRECTIVE_CMPP.md` Scope)

`MISSION_DIRECTIVE_CMPP.md` targeted and closed **Gap 1** (unconditional `CMPP21` Cantor-circulation smoothing, universal reversible Turing simulation, and global `s4AdaptedPoisson` Hamiltonian flow realization **R5**). **Gap 2** from the `c530a68` audit remains an intentional architectural scope boundary from `MISSION_DIRECTIVE.md`:

- **Explicit $S^4$ Fibration Model**: `s4Fibration x = southPoleStereoInv (x₀, x₁)` maps `Sphere4` onto a cap of `Sphere2` with nonempty equatorial singular circle `{x₂ = x₃ = x₄ = 0}` where fibers collapse to points (definite-fold type), satisfying Theorem 1's literal rank-`2` / rank-`0` unimodular Jacobian–Poisson statement cleanly without gluing the local Auroux–Donaldson–Katzarkov (ADK) indefinite-fold, real Lefschetz, and wrinkled-cusp normal forms proved in `Fibration/LocalSingularModels.lean` into a global $T^2/S^2$ fibration on $S^4$.
- **General 4-Manifolds (`Corollary 2`)**: `WrinkledFibration` axiomatizes a smooth map to `Sphere2` with a regular trivialized product region (without restricting global critical-locus singularity types), and `AdmitsWrinkledOrBrokenLefschetzFibration M` remains an explicit typeclass hypothesis encoding the external Gay–Kirby / Lekili existence theorem on arbitrary closed oriented smooth 4-manifolds `M`.
