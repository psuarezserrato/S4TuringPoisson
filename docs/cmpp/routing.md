# CMPP Empirical Local-Model Routing Policy (`docs/cmpp/routing.md`)

Set by empirical calibration data from **Milestone GM1** (`docs/cmpp/gemma_calibration.md`, 40 stratified `S4TuringPoisson` lemmas across 171 compiler-verified attempts) per `MISSION_DIRECTIVE_CMPP.md` §6.5–§6.7.

---

## 1. Empirical Routing Thresholds & Tier Decisions

From `MISSION_DIRECTIVE_CMPP.md` §6.5:
- **`pass@5 >= 30%`** $\implies$ **`gemma-first`** (routed to local `gemma4:12B` via `tools/gemma_loop.py` first; enforced by Gate G8 `tools/check_gemma_provenance.py`)
- **`10% <= pass@5 < 30%`** $\implies$ **`gemma-draft-only`** (local model drafts optional skeletons/premises; not enforced by Gate G8)
- **`pass@5 < 10%`** $\implies$ **`frontier`** (routed directly to **Gemini 4 Carbon**; not enforced by Gate G8)

| Tier | Description | GM1 `pass@1` | GM1 `pass@5` | Mean Wall / Decl | Routing Policy (§6.5) | Gate G8 Enforced (`--tiers`) |
|---|---|---:|---:|---:|---|---|
| **T0** | Algebra, combinatorics, boilerplate: definition unfolding + `omega`/`simp`/`ext`/`rfl`, digit/base bounds, `shiftSeq`/`replaceDom`/`shiftDom3` wrappers, interval endpoint projections | **33.3%** (`5/15`) | **53.3%** (`8/15`) | 111.1 s | **`gemma-first`** | **YES (`--tiers T0`)** |
| **T1** | Structured routine: list/orbit induction (`listComp`, `listToDiskIsotopy`, `ReversibleTM.step^[n]`), `ContDiff`/continuity compositions, compact-set/tube topology, multi-branch TM step case analysis | **0.0%** (`0/15`) | **0.0%** (`0/15`) | 260.4 s | **`frontier`** | NO |
| **T2** | Core analysis, geometry & computability: Hamiltonian ODE flow exactness (`timeDependentFlowOf_eq_of_hasMFDerivAt`), Cartan pullback, `Real.ofDigits` prefix/tail series, Sliding Lemma & Relocation Theorem, Bennett reversibilization, universal `FinTM0`, $S^4$ Poisson-Hamiltonian lifting | **0.0%** (`0/10`) | **0.0%** (`0/10`) | 307.5 s | **`frontier`** | NO |

---

## 2. Gate G8 Provenance Enforcement (`tools/check_gemma_provenance.py`)

- **Default Enforced Tiers**: `--tiers T0` (locked as default in `tools/check_gemma_provenance.py`).
- **Rule for Every New `-- tier: T0` Declaration Added in a Milestone Diff (`main...HEAD`)**:
  1. Must be tagged `-- tier: T0` directly above the declaration in the `.lean` source file.
  2. Must have **either**:
     - `.agents/gemma_accepted/<sanitized_decl_name>.lean` containing the compiler-verified proof accepted by `tools/gemma_loop.py`, **or**
     - `.agents/gemma_escalations/<sanitized_decl_name>.json` recording **$\ge 5$ failed compiler-verified attempts** from `tools/gemma_loop.py` prior to frontier discharge by Gemini 4 Carbon.
  3. Both `.agents/gemma_accepted/` and `.agents/gemma_escalations/` are tracked in Git (while `.agents/gemma_scratch/`, `.agents/gemma_usage.jsonl`, and `.agents/bm25_index.pkl` remain git-ignored).
- **Rule for `-- tier: T1` and `-- tier: T2` Declarations**:
  - Proved directly on **Gemini 4 Carbon** (`frontier`) using the LSP-first proof loop (`lean_goal`, `lean_diagnostic_messages`, `lean_local_search`, `lean_loogle`, `lean_multi_attempt`).
  - Frontier workers may still optionally query `python3 tools/s4tp_index.py query "<goal>"` for fast offline BM25 premise retrieval across the 50,851 indexed declarations.

---

## 3. Milestone-by-Milestone Routing Map (Waves W1–W4)

Note: Per Milestone C0 (`docs/cmpp/geometry_spec.md`), **I1 (chart rescaling, Milestone A0) is NOT needed** (`cantorDiskEmbed` remains 100% frozen).

| Milestone | Target File | Primary Tier Mix | Routing Policy & Execution Pattern |
|---|---|---|---|
| **A1** (Digit algebra, cylinder rectangles, **G0**, $A_w$ affine formulas) | `S4TuringPoisson/Smoothing/CMPP/Digits.lean` | **T0 + T2** | **Hybrid (`gemma-first` on T0 + Carbon on T2)**: Carbon writes the module skeleton and tags all digit/base/index arithmetic, `shiftSeq`/`replaceDom`/`mkDom3` projections, and affine map $A_w$ coordinate projection lemmas `-- tier: T0` for `tools/gemma_loop.py` (`gemma-first`), while proving `Real.ofDigits` tail shift formulas and **Lemma G0** (`image_rects_disjoint`) on Carbon (`-- tier: T2`). |
| **A2** (L1 autonomous compact-set translation + L2 rectangle hyperbolic stretch wrapper) | `S4TuringPoisson/Smoothing/CMPP/Primitives.lean` | **T2** (with T0 simp helpers) | **Frontier (`Carbon`)**: Smooth Urysohn cutoff construction on compact tubes, `hamiltonianVectorField_planeAreaForm_eq_of_hasFDerivAt`, `timeDependentFlowOf_eq_of_hasMFDerivAt`, and L2 rectangle-to-ball diameter bounds (`-- tier: T2`). Trivial `@[simp]` coordinate projections tagged `-- tier: T0` go through `gemma_loop.py`. |
| **A3** (1D Horizontal Sliding Lemma, slot coordinates, **Relocation Theorem RT**) | `S4TuringPoisson/Smoothing/CMPP/Relocation.lean` | **T0 + T1 + T2** | **Hybrid (`gemma-first` on T0 + Carbon on T1/T2)**: Slot coordinate bounds, box inclusion inequalities (`Box_src`, `Box_stage`, `Box_park`, `r₀ = 0.85`), and 1D interval separation arithmetic are tagged `-- tier: T0` (`gemma-first`); list induction over `listToDiskIsotopy` (`-- tier: T1`) and the inductive Relocation Theorem (`-- tier: T2`) are proved on Carbon. |
| **A4** (`RealizesGeneralizedShiftByHamiltonians` for injective `shiftDom3` shifts; **R4** `hasCMPP_of_simulator`) | `S4TuringPoisson/Smoothing/CMPP/Realize.lean` | **T1 + T2** (with T0 wrappers) | **Frontier (`Carbon`)**: Wires A1 (G0 + $A_w$ on $N^3$ cylinders) into A3 (Relocation Theorem) to deliver interim checkpoint **R4** (`hasCMPP_of_simulator`). Any routine T0 projection wrappers go through `gemma_loop.py`. |
| **B1** (Bennett 1973 generic reversibilization of `FinTM0`) | `S4TuringPoisson/Dynamics/Reversible/Bennett.lean` | **T0 + T1 + T2** | **Hybrid (`gemma-first` on T0 + Carbon on T1/T2)**: Finite state/history alphabet `DecidableEq`/`Fintype`/`Equiv` projection lemmas and `ShiftDir` simp lemmas tagged `-- tier: T0` (`gemma-first`); `stepPerm` bijectivity and forward/inverse history-track orbit equivalence (`-- tier: T1`/`T2`) on Carbon. |
| **B2** (Universal `FinTM0` with windowed output via `TuringRecursive` T-E) | `S4TuringPoisson/Dynamics/Reversible/Universal.lean` | **T0 + T1 + T2** | **Hybrid (`gemma-first` on T0 + Carbon on T1/T2)**: Alphabet/state transport ` @[simp]` projections from `TuringRecursive` tagged `-- tier: T0` (`gemma-first`); `HaltsWithWindow` transport and simulation equivalence (`-- tier: T2`) on Carbon. |
| **B3** (Refactor I2 & construct `UniversalReversibleSimulator`) | `S4TuringPoisson/Smoothing/CMPP/Simulator.lean` | **T1 + T2** (with T0 helpers) | **Frontier (`Carbon`)**: Assembles B1 + B2 + primitive-recursive initial digit enumerators into `UniversalReversibleSimulator` (`-- tier: T1`/`T2`), routing T0 digit/index arithmetic helpers to `gemma_loop.py`. |
| **P** (**R5** Poisson-Hamiltonian realization on $S^4$) | `S4TuringPoisson/Extension/PoissonHamiltonian.lean` | **T2** | **Frontier (`Carbon`)**: Lifts autonomous planar Hamiltonians via $\tilde{H}_P(\Phi^{-1}(b, C.\mathrm{embed}\,y)) = (\rho(b) \cdot C.\mathrm{areaScale}) \cdot P.H(0, y)$, proves $d_B \tilde{H}_P \wedge f^* \mu_B = 0$ on 2D `Sphere2`, and establishes time-1 flow composition on $S^4$ (`-- tier: T2`). |
| **Z** (Final unconditional instance **R1**, **R2–R3** `Main.lean` & `CompChecks.lean`, `#audit_wiring`, `AUDIT.md`) | `S4TuringPoisson/Smoothing/CMPPInstance.lean`, `Main.lean`, `Checks/CompChecks.lean` | **T2** | **Frontier (`Carbon`)**: Final assembly and verification gates G1–G9 (`bash tools/collect_axioms.sh --wiring ...`, `python3 tools/check_gemma_provenance.py main...HEAD --tiers T0`). |

---

## 4. 24 GB Unified RAM Concurrency & Daemon Protocol

1. **Max 2 Active Lean Processes**: The `gemma_loop.py` daemon's `LEAN_NUM_THREADS=2 lake env lean` check counts as **1 slot**; at most **1 frontier Lean worker** may run concurrently on the second slot (with all other workers parked in `waiting`).
2. **Zero Idle Metal Footprint (`"keep_alive": 0`)**: Every call through `tools/ollama_lean4_client.py` / `tools/gemma_loop.py` passes numeric `"keep_alive": 0`, unloading `gemma4:12B` immediately after token generation so `ollama` and `lake env lean` never contend for unified RAM.
3. **Swap Guardrail (`10240M` / `10 GB`)**: Workers must run `python3 tools/workflow_control.py check-pause` before heavy runs and check `sysctl vm.swapusage` + `ollama ps`.
