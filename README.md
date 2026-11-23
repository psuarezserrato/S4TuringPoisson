# S4TuringPoisson

A Lean 4 formalization of Pablo Suárez-Serrato, *"Hamiltonian and Turing complete flows on smooth 4-manifolds"* ([S4TCdiffeo-Aug-2026.tex](S4TCdiffeo-Aug-2026.tex)), together with an unconditional formalization of the area-preserving disk smoothing theorem of Cardona–Miranda–Peralta-Salas–Presas (`CMPP21`, Theorem 5.2) via Bennett's reversible Turing machine compiler and a universal `TM0` simulator, and explicit Poisson–Hamiltonian time-1 flow realization on $S^4$.

- **Lean toolchain**: `leanprover/lean4:v4.36.0` (`autoImplicit = false`, `relaxedAutoImplicit = false`)
- **Geometry library**: [`TauCeti`](https://github.com/TauCetiProject/TauCeti) (`v4.36.0` @ `d91980bdc2`) + `Mathlib` (`fc4f59e577`)
- **Computability library**: [`Turing-recursive`](https://github.com/psuarezserrato/Turing-recursive) (`../Turing-recursive`)
- **License**: GNU Affero General Public License v3.0 (AGPLv3) for non-commercial use ([LICENSE.md](LICENSE.md))

---

## Headline Deliverables (`R1`–`R5`, zero custom axioms)

| ID | Declaration | Module | Status |
|---|---|---|---|
| **R1** | `instHasCMPPCantorCirculationHamiltonians` | [`Smoothing/CMPPInstance.lean`](S4TuringPoisson/Smoothing/CMPPInstance.lean) | **UNCONDITIONAL** (`0` binders) |
| **R2** | `Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_S4`, `Main.exists_turingComplete_volumePreserving_diffeomorph_S4`, `Main.undecidable_orbit_reachability_S4`, `Main.exists_turingComplete_volumePreserving_poissonDiffeomorph_fourManifold` | [`Main.lean`](S4TuringPoisson/Main.lean) | **UNCONDITIONAL** on `Sphere4` (`0` binders); `[AdmitsWrinkledOrBrokenLefschetzFibration M]` on general 4-manifolds |
| **R3** | `Checks.gate6_sphere4_witness`, `Checks.gate6_poisson_hamiltonian_realization_S4`, & audit | [`Checks/CompChecks.lean`](S4TuringPoisson/Checks/CompChecks.lean), [`AUDIT.md`](AUDIT.md) | **UNCONDITIONAL** (`0` binders) |
| **R4** | `hasCMPP_of_simulator`, `hasCMPP_of_simulator_isAutonomous` | [`Smoothing/CMPP/Realize.lean`](S4TuringPoisson/Smoothing/CMPP/Realize.lean) | **CONDITIONAL-ON-`UniversalReversibleSimulator`** (interim reduction) |
| **R5** | `exists_poisson_hamiltonian_realization_S4` | [`Extension/PoissonHamiltonian.lean`](S4TuringPoisson/Extension/PoissonHamiltonian.lean) | **UNCONDITIONAL** (`0` binders; composition of time-1 `s4AdaptedPoisson` flows) |

All headline theorems use exclusively Lean's three standard axioms `{propext, Classical.choice, Quot.sound}` (`0` `sorry`, `0` custom axioms).

---

## Repository Layout

| Directory / File | Contents |
|---|---|
| `S4TuringPoisson/Interfaces.lean` | Core interfaces: `PositiveVolumeForm`, `FinTM0`, `HaltsWithWindow`, `IsTuringComplete` |
| `S4TuringPoisson/Poisson/` | Smooth bivectors, modular class & unimodularity, Jacobian Poisson structures, singular circle normal forms |
| `S4TuringPoisson/Fibration/` | Local singular models (`indefiniteFoldMap`, `realLefschetzMap`, `wrinkledCuspMap`), `s4Fibration`, Darboux disk charts |
| `S4TuringPoisson/Dynamics/` | `GeneralizedShift`, `ReversibleTM`, Cantor square embedding `cantorDiskEmbed`, transfer, undecidability, `Bennett.lean`, `Universal.lean` |
| `S4TuringPoisson/Smoothing/` | Planar Hamiltonian ODE engine (`DiskSmoothing.lean`), `CMPP/{Digits,Primitives,Relocation,Realize,Simulator}.lean`, global `CMPPInstance.lean` |
| `S4TuringPoisson/Extension/` | `AlignedUnimodularVolume.lean` (Eq. 1), `BumpIsotopyLift.lean`, `PoissonHamiltonian.lean` (R5 time-1 flows) |
| `S4TuringPoisson/Main.lean` | Headline Theorem 1, Corollary 2, undecidability on $S^4$, and parametric `*_of_cmpp` corollaries |
| `S4TuringPoisson/Checks/` | Anti-vacuity checks (`GeomChecks.lean`, `CompChecks.lean`) |
| `blueprint/` & `report/` | `leanblueprint` source, interactive dependency graph, `print.pdf`, and executive audit report (`final_executive_report.pdf`) |
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
