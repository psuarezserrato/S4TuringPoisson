# S4TuringPoisson

A Lean 4 formalization of Pablo Suárez-Serrato, *"Hamiltonian and Turing complete flows on smooth 4-manifolds"* ([S4TCdiffeo-Aug-2026.tex](S4TCdiffeo-Aug-2026.tex)), together with an unconditional formalization of the area-preserving disk smoothing theorem of Cardona–Miranda–Peralta-Salas–Presas (`CMPP21`, Theorem 5.2), explicit planar Lekili (2009) wrinkled-fibration moves and broken-to-wrinkled surgery, the global Auroux–Donaldson–Katzarkov (ADK05) broken Lefschetz fibration on $S^4$, and unconditional Corollary 2 on closed oriented smooth 4-manifolds.

- **Lean toolchain**: `leanprover/lean4:v4.36.0` (`autoImplicit = false`, `relaxedAutoImplicit = false`)
- **Geometry library**: [`TauCeti`](https://github.com/TauCetiProject/TauCeti) (`v4.36.0` @ `d91980bdc`) + `Mathlib` (`fc4f59e5`)
- **Computability library**: [`Turing-recursive`](https://github.com/psuarezserrato/Turing-recursive) (`../Turing-recursive`, `4120346`)
- **Verification**: `10,130` build jobs, `29` modules (`41,361` LOC), `35/35` `leanchecker` leaf modules, `54/54` green blueprint nodes (`128` tracked declarations), `0` custom axioms
- **License**: GNU Affero General Public License v3.0 (AGPLv3) for non-commercial use ([LICENSE.md](LICENSE.md))

---

## Headline Deliverables (Zero Custom Axioms)

| ID | Declaration | Module | Status |
|---|---|---|---|
| **R1** | `instHasCMPPCantorCirculationHamiltonians` | [`Smoothing/CMPPInstance.lean`](S4TuringPoisson/Smoothing/CMPPInstance.lean) | **UNCONDITIONAL** (`0` binders) |
| **R2 ($S^4$)** | `Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_S4`, `Main.exists_turingComplete_volumePreserving_diffeomorph_S4`, `Main.undecidable_orbit_reachability_S4` | [`Main.lean`](S4TuringPoisson/Main.lean) | **UNCONDITIONAL** on `Sphere4` (`0` binders) |
| **LW4 (ADK $S^4$)** | `s4BrokenLefschetzFibration`, `exists_turingComplete_volumePreserving_poissonDiffeomorph_S4_ADK`, `exists_poisson_hamiltonian_realization_S4_ADK` | [`Fibration/ADKS4Fibration.lean`](S4TuringPoisson/Fibration/ADKS4Fibration.lean) | **UNCONDITIONAL** on `Sphere4` (`0` binders; Track A global ADK indefinite-fold fibration) |
| **LW1 / LW3** | `PurelyWrinkledFibration`, `lekiliMove1`–`lekiliMove4`, `BrokenLefschetzFibration.exists_purelyWrinkledFibration` | [`Fibration/PurelyWrinkled.lean`](S4TuringPoisson/Fibration/PurelyWrinkled.lean), [`Fibration/LekiliMoves.lean`](S4TuringPoisson/Fibration/LekiliMoves.lean) | **UNCONDITIONAL** on compact broken Lefschetz fibrations (Track A) |
| **LW2 (Cor. 2)** | `Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_closedFourManifold`, `Main.undecidable_orbit_reachability_closedFourManifold`, `exists_poisson_hamiltonian_realization_closedFourManifold` | [`Fibration/ClosedManifoldLocal.lean`](S4TuringPoisson/Fibration/ClosedManifoldLocal.lean), [`Main.lean`](S4TuringPoisson/Main.lean), [`Extension/PoissonHamiltonian.lean`](S4TuringPoisson/Extension/PoissonHamiltonian.lean) | **UNCONDITIONAL** on `(M, V_M)` (zero fibration typeclasses; Track B coordinate-ball `WrinkledFibration`) |
| **R3 / Gates 5–6** | `Checks.gate51_*`, `Checks.gate52_*`, `Checks.gate53_*`, `Checks.gate6_*`, `Checks.unconditional_corollary2_*` | [`Checks/GeomChecks.lean`](S4TuringPoisson/Checks/GeomChecks.lean), [`Checks/CompChecks.lean`](S4TuringPoisson/Checks/CompChecks.lean) | **UNCONDITIONAL** (`0` binders) |
| **R5** | `exists_poisson_hamiltonian_realization_S4` | [`Extension/PoissonHamiltonian.lean`](S4TuringPoisson/Extension/PoissonHamiltonian.lean) | **UNCONDITIONAL** (`0` binders; composed time-1 Hamiltonian flows) |

All headline theorems use exclusively Lean's three standard axioms `{propext, Classical.choice, Quot.sound}` (`0` `sorry`, `0` custom axioms).

---

## Repository Layout

| Directory / File | Contents |
|---|---|
| `S4TuringPoisson/Interfaces.lean` | Core interfaces: `PositiveVolumeForm`, `FinTM0`, `HaltsWithWindow`, `IsTuringComplete` |
| `S4TuringPoisson/Poisson/` | Smooth bivectors, modular class & unimodularity, Jacobian Poisson structures, singular circle normal forms |
| `S4TuringPoisson/Fibration/` | Local singular models, `s4Fibration`, `PurelyWrinkledFibration`, Lekili Moves 1–4 & surgery (`LekiliMoves.lean`), global ADK $S^4$ (`ADKS4Fibration.lean`), Track B closed 4-manifold constructor (`ClosedManifoldLocal.lean`) |
| `S4TuringPoisson/Dynamics/` | `GeneralizedShift`, `ReversibleTM`, Cantor square embedding `cantorDiskEmbed`, transfer, undecidability, `Bennett.lean`, `Universal.lean` |
| `S4TuringPoisson/Smoothing/` | Planar Hamiltonian ODE engine (`DiskSmoothing.lean`), `CMPP/{Digits,Primitives,Relocation,Realize,Simulator}.lean`, global `CMPPInstance.lean` |
| `S4TuringPoisson/Extension/` | `AlignedUnimodularVolume.lean` (Eq. 1), `BumpIsotopyLift.lean`, `PoissonHamiltonian.lean` (R5 time-1 flows) |
| `S4TuringPoisson/Main.lean` | Headline Theorem 1, unconditional & parametric Corollary 2, undecidability on $S^4$ and $(M, V_M)$ |
| `S4TuringPoisson/Checks/` | Anti-vacuity checks (`GeomChecks.lean`, `CompChecks.lean`) |
| `blueprint/` & `report/` | `leanblueprint` source (`54/54` green), interactive dependency graph, `print.pdf`, and executive audit report (`final_executive_report.pdf`) |
| `tools/` & `tests/` | Axiom census + DAG-memoized `#audit_wiring` (`audit_axioms.lean`), `gemma4:12B` prover/ledger, `unittest` suite |

---

## Local Build & Verification

Because `lakefile.toml` references `TuringRecursive` via `path = "../Turing-recursive"`, clone both repositories side by side in the same parent directory:

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
  S4TuringPoisson.instHasCMPPCantorCirculationHamiltonians \
  CompactlySupportedPlanarHamiltonian.toDiskIsotopy,S4TuringPoisson.CMPP.exists_relocation_hamiltonians,S4TuringPoisson.Reversible.bennettReversibleTM,TuringRecursive.U
python3 -m unittest discover -s tests -q
```

---

## Blueprint, Reports & Directives

- **Executive Audit Report**: [`report/final_executive_report.pdf`](report/final_executive_report.pdf) ([`.tex`](report/final_executive_report.tex)) & [`AUDIT.md`](AUDIT.md)
- **Interactive Blueprint & Graph**: [`blueprint/web/dep_graph_document.html`](blueprint/web/dep_graph_document.html), [`blueprint/print/print.pdf`](blueprint/print/print.pdf), [`report/blueprint_dep_graph.pdf`](report/blueprint_dep_graph.pdf)
- **Mission Directives**: [`MISSION_DIRECTIVE.md`](MISSION_DIRECTIVE.md), [`MISSION_DIRECTIVE_CMPP.md`](MISSION_DIRECTIVE_CMPP.md), [`MISSION_DIRECTIVE_TMPARTREC.md`](MISSION_DIRECTIVE_TMPARTREC.md), [`MISSION_DIRECTIVE_LEKILI.md`](MISSION_DIRECTIVE_LEKILI.md)

---

## License & Citation

Licensed under the **GNU Affero General Public License v3.0 (AGPLv3)** for non-commercial use — see [LICENSE.md](LICENSE.md) for details:

> This project is licensed under non-commercial use. If you wish to use this software in a commercial product, service, or enterprise environment, please contact the developer to purchase a commercial license or negotiate royalty terms.

Authored by **Pablo Suárez-Serrato** (November 2026).
