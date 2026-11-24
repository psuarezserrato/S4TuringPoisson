# S4TuringPoisson

A Lean 4 formalization of Pablo Suárez-Serrato, *"Hamiltonian and Turing complete flows on smooth 4-manifolds"* ([S4TCdiffeo-Aug-2026.tex](S4TCdiffeo-Aug-2026.tex)), together with an unconditional formalization of the area-preserving disk smoothing theorem of Cardona–Miranda–Peralta-Salas–Presas (`CMPP21`, Theorem 5.2), explicit local $\mathbb{R}^4 \to \mathbb{R}^2$ Lekili (2009) wrinkled-fibration moves and compactly supported broken-to-purely-wrinkled homotopy, the global Auroux–Donaldson–Katzarkov (`ADK05`) broken Lefschetz fibration on $S^4$ (with smooth $S^2$ and $T^2$ fiber diffeomorphisms), componentwise Moser (`Mos65`) volume conjugation, and both the unconditional exact-volume closed 4-manifold Corollary 2 and the generically rank-2 `PurelyWrinkledFibration` / `BrokenLefschetzFibration` Corollary 2.

This project builds on and uses the companion computability library [`https://github.com/psuarezserrato/Turing-recursive`](https://github.com/psuarezserrato/Turing-recursive) for the universal `TM0` machine `U` and partial-recursive computability foundations.

- **Lean toolchain**: `leanprover/lean4:v4.36.0` (`autoImplicit = false`, `relaxedAutoImplicit = false`)
- **Geometry library**: [`TauCeti`](https://github.com/TauCetiProject/TauCeti) (`v4.36.0` @ `d91980bdc`) + `Mathlib` (`fc4f59e5`)
- **Computability library**: [`https://github.com/psuarezserrato/Turing-recursive`](https://github.com/psuarezserrato/Turing-recursive) (`../Turing-recursive`, `4120346`)
- **Verification**: `10,266` build jobs, `30` modules (`51,058` LOC), `36/36` `leanchecker` leaf modules, `56/56` green blueprint nodes (`163` tracked declarations), `0` custom axioms (**Sound and Complete**)
- **License**: GNU Affero General Public License v3.0 (AGPLv3) for non-commercial use ([LICENSE.md](LICENSE.md))

---

## Headline Deliverables (Zero Custom Axioms)

| ID | Declaration | Module | Status |
|---|---|---|---|
| **R1** | `instHasCMPPCantorCirculationHamiltonians` | [`Smoothing/CMPPInstance.lean`](S4TuringPoisson/Smoothing/CMPPInstance.lean) | **UNCONDITIONAL** (`0` binders) |
| **R2 ($S^4$)** | `Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_S4`, `Main.exists_turingComplete_exactVolumePreserving_poissonDiffeomorph_S4`, `Main.undecidable_orbit_reachability_S4` | [`Main.lean`](S4TuringPoisson/Main.lean) | **UNCONDITIONAL** on `Sphere4` (`0` binders; aligned & exact round $\Omega_{S^4}$) |
| **LW4 / SC3 (ADK $S^4$)** | `s4BrokenLefschetzFibration`, `s4ADKTorusBrokenLefschetzFibration`, `s4ADKNorthFiberDiffeomorph`, `s4ADKTorusFiberDiffeomorph`, `exists_turingComplete_volumePreserving_poissonDiffeomorph_S4_ADK`, `Main.exists_turingComplete_exactVolumePreserving_poissonDiffeomorph_S4_ADK` | [`Fibration/ADKS4Fibration.lean`](S4TuringPoisson/Fibration/ADKS4Fibration.lean), [`Main.lean`](S4TuringPoisson/Main.lean) | **UNCONDITIONAL** on `Sphere4` (`0` binders; Track A global ADK indefinite-fold fibration, smooth $S^2$/$T^2$ fibers) |
| **LW1 / LW3 / SC2** | `PurelyWrinkledFibration`, `lekiliMove1`–`lekiliMove4`, `BrokenLefschetzFibration.exists_purelyWrinkledFibration` | [`Fibration/PurelyWrinkled.lean`](S4TuringPoisson/Fibration/PurelyWrinkled.lean), [`Fibration/LekiliMoves.lean`](S4TuringPoisson/Fibration/LekiliMoves.lean) | **UNCONDITIONAL** on compact broken Lefschetz fibrations (compact support $K$ + smooth homotopy $H$) |
| **SC2 / SC3 / SC4 (Track A Cor. 2)** | `Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_of_purelyWrinkled`, `..._of_brokenLefschetz`, `Main.exists_turingComplete_exactVolumePreserving_poissonDiffeomorph_of_purelyWrinkled` | [`Main.lean`](S4TuringPoisson/Main.lean), [`Extension/MoserVolume.lean`](S4TuringPoisson/Extension/MoserVolume.lean) | Positively co-oriented `PurelyWrinkledFibration` / `BrokenLefschetzFibration` (`IsGenericallyRankTwo`, open dense rank-2 locus, exact `V_M.Ω`) |
| **LW2 / SC4 (Literal Cor. 2)** | `Main.exists_turingComplete_exactVolumePreserving_diffeomorph_closedFourManifold`, `Main.exists_turingComplete_exactVolumePreserving_poissonDiffeomorph_closedFourManifold`, `Main.undecidable_orbit_reachability_exactVolumePreserving_closedFourManifold` | [`Extension/MoserVolume.lean`](S4TuringPoisson/Extension/MoserVolume.lean), [`Fibration/ClosedManifoldLocal.lean`](S4TuringPoisson/Fibration/ClosedManifoldLocal.lean), [`Main.lean`](S4TuringPoisson/Main.lean) | **UNCONDITIONAL** on `(M, V_M)` (zero fibration or connectedness assumptions; preserves `V_M.Ω` and `V_M.μ` identically) |
| **R3 / Gates 5–6** | `Checks.gate51_*`–`Checks.gate54_*`, `Checks.gate6_*`, `Checks.periodic_rotation_not_isTuringComplete`, `Checks.closedManifoldLocal_not_genericallyRankTwo`, `Checks.exact_moser_volume_*` | [`Checks/GeomChecks.lean`](S4TuringPoisson/Checks/GeomChecks.lean), [`Checks/CompChecks.lean`](S4TuringPoisson/Checks/CompChecks.lean) | **UNCONDITIONAL** (`0` binders) |
| **R5** | `exists_poisson_hamiltonian_realization_S4`, `exists_exactVolumePreserving_poisson_hamiltonian_realization_S4`, `..._S4_ADK`, `..._closedFourManifold` | [`Extension/PoissonHamiltonian.lean`](S4TuringPoisson/Extension/PoissonHamiltonian.lean), [`Extension/MoserVolume.lean`](S4TuringPoisson/Extension/MoserVolume.lean) | **UNCONDITIONAL** (`0` binders on $S^4$; composed time-1 Poisson–Hamiltonian flows) |

All headline theorems use exclusively Lean's three standard axioms `{propext, Classical.choice, Quot.sound}` (`0` `sorry`, `0` custom axioms).

---

## Repository Layout

| Directory / File | Contents |
|---|---|
| `../Turing-recursive/` | Companion Lean 4 computability library ([`https://github.com/psuarezserrato/Turing-recursive`](https://github.com/psuarezserrato/Turing-recursive)) that `S4TuringPoisson` builds on (`lakefile.toml`) for the universal `TM0` machine `U`, `Partrec` equivalence, and tape encodings |
| `S4TuringPoisson/Interfaces.lean` | Core interfaces: `PositiveVolumeForm`, `FinTM0`, `HaltsWithWindow`, `RatBox2`, effective `TuringCompleteWitness` (`openChart`, `computable_encodeOpen`, `orbit_encodePoint_injective`), `IsTuringComplete` |
| `S4TuringPoisson/Poisson/` | Smooth bivectors, modular class & unimodularity, Jacobian Poisson structures & `IsGenericallyRankTwo`, singular circle normal forms |
| `S4TuringPoisson/Fibration/` | Local singular models & chirality, `RegularDiskFibration`, `s4Fibration`, `PurelyWrinkledFibration`, Lekili Moves 1–4 & compactly supported homotopy (`LekiliMoves.lean`), global ADK $S^4$ (`ADKS4Fibration.lean`), Track B closed 4-manifold constructor (`ClosedManifoldLocal.lean`) |
| `S4TuringPoisson/Dynamics/` | `GeneralizedShift`, `ReversibleTM`, Cantor square embedding `cantorDiskEmbed`, transfer, undecidability, `Bennett.lean`, `Universal.lean` |
| `S4TuringPoisson/Smoothing/` | Planar Hamiltonian ODE engine (`DiskSmoothing.lean`), `CMPP/{Digits,Primitives,Relocation,Realize,Simulator}.lean`, global `CMPPInstance.lean` |
| `S4TuringPoisson/Extension/` | `AlignedUnimodularVolume.lean` (Eq. 1), `BumpIsotopyLift.lean`, `PoissonHamiltonian.lean` (R5 time-1 flows), `MoserVolume.lean` (componentwise Moser exact volume conjugation) |
| `S4TuringPoisson/Main.lean` | Headline Theorem 1 (aligned & exact round volume), Track A `PurelyWrinkled`/`BrokenLefschetz` Corollary 2 (`IsGenericallyRankTwo`), unconditional exact-`V_M` closed 4-manifold Corollary 2, and undecidability |
| `S4TuringPoisson/Checks/` | Adversarial anti-vacuity and refutation checks (`GeomChecks.lean`, `CompChecks.lean`) |
| `blueprint/` & `report/` | `leanblueprint` source (`56/56` green), interactive dependency graph, `print.pdf`, and executive audit report (`final_executive_report.pdf`) |
| `tools/` & `tests/` | Axiom census + DAG-memoized `#audit_wiring` (`audit_axioms.lean`), `gemma4:12B` prover/ledger, `unittest` suite |

---

## Local Build & Verification

`S4TuringPoisson` builds on and uses [`https://github.com/psuarezserrato/Turing-recursive`](https://github.com/psuarezserrato/Turing-recursive) (`path = "../Turing-recursive"` in `lakefile.toml`). Clone both repositories side by side in the same parent directory:

```text
.
├── Turing-recursive/   # https://github.com/psuarezserrato/Turing-recursive
└── S4TuringPoisson/    # builds on ../Turing-recursive via lakefile.toml
```

```bash
git clone https://github.com/psuarezserrato/Turing-recursive.git
git clone https://github.com/psuarezserrato/S4TuringPoisson.git
cd S4TuringPoisson
```

Build, audit axioms, inspect transitive proof wiring, and run tooling tests:

```bash
LEAN_NUM_THREADS=2 lake build --wfail
LEAN_NUM_THREADS=2 bash tools/collect_axioms.sh
LEAN_NUM_THREADS=2 bash tools/collect_axioms.sh --wiring \
  S4TuringPoisson.Main.exists_turingComplete_exactVolumePreserving_diffeomorph_closedFourManifold \
  TauCeti.mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero,S4TuringPoisson.MoserVolume.ofPositivelyCooriented,S4TuringPoisson.instHasCMPPCantorCirculationHamiltonians,TuringRecursive.U
python3 -m unittest discover -s tests -q
```

---

## Blueprint, Reports & Directives

- **Executive Audit Report**: [`report/final_executive_report.pdf`](report/final_executive_report.pdf) ([`.tex`](report/final_executive_report.tex)) & [`AUDIT.md`](AUDIT.md)
- **Interactive Blueprint & Graph**: [`blueprint/web/dep_graph_document.html`](blueprint/web/dep_graph_document.html), [`blueprint/print/print.pdf`](blueprint/print/print.pdf), [`report/blueprint_dep_graph.pdf`](report/blueprint_dep_graph.pdf)
- **Mission Directives**: [`MISSION_DIRECTIVE.md`](MISSION_DIRECTIVE.md), [`MISSION_DIRECTIVE_CMPP.md`](MISSION_DIRECTIVE_CMPP.md), [`MISSION_DIRECTIVE_TMPARTREC.md`](MISSION_DIRECTIVE_TMPARTREC.md), [`MISSION_DIRECTIVE_LEKILI.md`](MISSION_DIRECTIVE_LEKILI.md), [`MISSION_DIRECTIVE_SOUND_AND_COMPLETE.md`](MISSION_DIRECTIVE_SOUND_AND_COMPLETE.md)

---

## License & Citation

Licensed under the **GNU Affero General Public License v3.0 (AGPLv3)** for non-commercial use — see [LICENSE.md](LICENSE.md) for details:

> This project is licensed under non-commercial use. If you wish to use this software in a commercial product, service, or enterprise environment, please contact the developer to purchase a commercial license or negotiate royalty terms.

Authored by **Pablo Suárez-Serrato** (November 2026).
