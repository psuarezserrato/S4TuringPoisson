/-
Copyright (c) 2026 Pablo Suárez-Serrato. All rights reserved.
Released under the GNU Affero General Public License v3.0 (AGPLv3) for non-commercial use;
see LICENSE.md for details.
This project is licensed under non-commercial use. If you wish to use this software in a
commercial product, service, or enterprise environment, please contact the developer to purchase
a commercial license or negotiate royalty terms.
Authored by Pablo Suárez-Serrato (November 2026).
-/
module

public import S4TuringPoisson.Smoothing.CMPP.Realize
public import S4TuringPoisson.Smoothing.CMPP.Simulator

/-!
# Unconditional `HasCMPPCantorCirculationHamiltonians` Instance (CMPP Milestone Z / Deliverable R1)

This module formalizes **Deliverable R1 (`UNCONDITIONAL`)** of `MISSION_DIRECTIVE_CMPP.md` (§1, §7,
§8), discharging the global `HasCMPPCantorCirculationHamiltonians` typeclass with **zero**
external hypotheses or custom axioms by feeding Milestone B3's unconditional
`universalReversibleSimulator : UniversalReversibleSimulator` into Milestone A4's smooth autonomous
Hamiltonian realization `hasCMPP_of_simulator`:

1. **`instHasCMPPCantorCirculationHamiltonians` (`UNCONDITIONAL`, Deliverable R1)**:
   - Global `[instance]` of `HasCMPPCantorCirculationHamiltonians` supported inside
     `Metric.ball 0 CMPP.cmppR0` (`CMPP.cmppR0 = 17 / 20`), automatically activating
     `instHasTuringCompleteAreaPreservingDiskIsotopyOfCMPP` across `Main.lean` and
     `Checks/CompChecks.lean`.
2. **Definitional & Autonomy Projections**:
   - `instHasCMPPCantorCirculationHamiltonians_eq`,
     `instHasCMPPCantorCirculationHamiltonians_sim`,
     `instHasCMPPCantorCirculationHamiltonians_r₀`,
     `instHasCMPPCantorCirculationHamiltonians_generators`, and
     `instHasCMPPCantorCirculationHamiltonians_isAutonomous`.
-/

@[expose] public section

namespace S4TuringPoisson

/-- **Deliverable R1 (`UNCONDITIONAL`, `MISSION_DIRECTIVE_CMPP.md` §1 & Milestone Z)**:
Global unconditional instance of `HasCMPPCantorCirculationHamiltonians`, realizing the generalized
shift of Bennett's universal reversible Turing machine (`universalReversibleSimulator`) on the
square Cantor set `cantorDiskEmbed` via a finite list of compactly supported **autonomous** planar
Hamiltonians inside `Metric.ball 0 CMPP.cmppR0` (`CMPP.cmppR0 = 17 / 20`). -/
noncomputable instance instHasCMPPCantorCirculationHamiltonians :
    HasCMPPCantorCirculationHamiltonians :=
  hasCMPP_of_simulator universalReversibleSimulator

/-- Definitional unfolding of `instHasCMPPCantorCirculationHamiltonians` as
`hasCMPP_of_simulator universalReversibleSimulator` (`UNCONDITIONAL`). -/
-- tier: T0
theorem instHasCMPPCantorCirculationHamiltonians_eq :
    instHasCMPPCantorCirculationHamiltonians =
      hasCMPP_of_simulator universalReversibleSimulator := by
  rfl

/-- Underlying `UniversalReversibleSimulator` of `instHasCMPPCantorCirculationHamiltonians` is
`universalReversibleSimulator` (`UNCONDITIONAL`). -/
-- tier: T0
@[simp]
theorem instHasCMPPCantorCirculationHamiltonians_sim :
    instHasCMPPCantorCirculationHamiltonians.sim = universalReversibleSimulator :=
  rfl

/-- Compact-support radius of `instHasCMPPCantorCirculationHamiltonians` is
`CMPP.cmppR0 = 17 / 20` (`UNCONDITIONAL`). -/
-- tier: T0
theorem instHasCMPPCantorCirculationHamiltonians_r₀ :
    instHasCMPPCantorCirculationHamiltonians.r₀ = CMPP.cmppR0 := by
  rfl

/-- Planar Hamiltonian generator list of `instHasCMPPCantorCirculationHamiltonians` coincides with
`universalReversibleSimulator_cmpp.generators` (`UNCONDITIONAL`). -/
-- tier: T0
theorem instHasCMPPCantorCirculationHamiltonians_generators :
    instHasCMPPCantorCirculationHamiltonians.generators =
      universalReversibleSimulator_cmpp.generators := by
  rfl

/-- Every planar Hamiltonian generator in `instHasCMPPCantorCirculationHamiltonians.generators` is
autonomous (`UNCONDITIONAL`). -/
-- tier: T1
theorem instHasCMPPCantorCirculationHamiltonians_isAutonomous :
    ∀ P ∈ instHasCMPPCantorCirculationHamiltonians.generators, P.IsAutonomous :=
  hasCMPP_of_simulator_isAutonomous universalReversibleSimulator

end S4TuringPoisson
