# MISSION DIRECTIVE (CMPP): Discharge `HasCMPPCantorCirculationHamiltonians`
## Merged directive v2: formalize the CMPP21 smoothing result as Hamiltonian flows, local-model-first

Repo: `/Users/pablosuarez/Desktop/S4TuringPoisson` (`main`, Lean `v4.36.0`, Mathlib + TauCeti `v4.36.0`).
Prior art repo: `/Users/pablosuarez/Desktop/SympTopAutoForm` (Mathlib `v4.35.0`, no TauCeti).
Inputs merged here: (a) my first draft of this directive, (b) `/Users/pablosuarez/.gemini/antigravity/brain/745c86d2-.../CMPP_MISSION_DIRECTIVE.md`,
(c) the user's decisions below. Standing rules from `MISSION_DIRECTIVE.md` §1.3, §2, §6 and `.agents/rules/lean-integrity.md` apply
(zero `sorry`/`axiom`, junk-value vigilance, exclusive file ownership, isolated `.worktrees/<worker>`, 5-retry escalation, 24 GB RAM guardrails).

---

## 0. Resolved decisions and how the two drafts were reconciled

| ID | User decision | Consequence in this directive |
|---|---|---|
| **D1** | **Hamiltonian flows are mandatory** (important for the theory) | Target is the CMPP class itself. Every generator is a `CompactlySupportedPlanarHamiltonian`. My Moser route (non-Hamiltonian) is demoted to an emergency appendix; the other draft's route (translations + exact stretch) is Hamiltonian by construction and is now the **main route** |
| **D2** | **No fixed-machine fallback.** Recreate a full universal machine as a Hamiltonian flow using Poisson geometry on S⁴ | `IsTuringComplete` stays universal over all `FinTM0`. The other draft's "D4 = `hasCMPP_of_simulator`" is kept only as an **interim, explicitly CONDITIONAL checkpoint (R4)**, never as an endpoint. New deliverable **R5**: the final diffeomorphism of S⁴ is exhibited as a composition of time-1 flows of **Poisson-Hamiltonian vector fields of π_f** (§4.5) |
| **D3** | Cantor-set design stays as is (improving Moore's shift is a separate project) | `cantorDiskEmbed`, base `2N−1`, digit scheme, `GeneralizedShift`, `shiftDom3` are **frozen**. The other draft's refactor I1 (chart scale) is **only allowed as a pure similarity rescaling with the default behaviour recoverable, and only after C0 proves it is necessary and the user signs off** (§5). Its I3 (conjugacy bypass) is **removed** (it would replace the Cantor design and escape D1) |
| **D4** | `gemma4:12B` was called only 7 times; maximize local use to cut wall-clock and frontier compute | New §6 **Local-Model-First Engine**: compiler-in-the-loop prover, retrieval, measured tiers, enforced provenance gate, outcome-logging ledger |

Naming fix: the other draft's deliverables "D1–D4" collided with the user's decisions. They are renamed **R1–R4** below; R5 is new.

Reconciled discrepancies:
1. *Geometry route*: other draft (Sliding Lemma + rigid translations + exact hyperbolic stretch) replaces my parametric Moser plan. Reasons: no Moser/isotopy-extension exists in TauCeti; the route reuses already-proved primitives; it yields Hamiltonians directly.
2. *Ledger evidence*: the other draft cites the gromov campaign's 499 local calls as a good baseline. I checked: **all 499 records have `accepted = null`**, so that ledger shows usage but never recorded success. The new ledger must record verified outcomes (§6.4).
3. *Concurrency*: the 2-Lean-worker cap now includes the local-model daemon (§6.6).

---

## 1. Objective and deliverables

| ID | Deliverable | Label |
|---|---|---|
| **R1 (main)** | `noncomputable instance : HasCMPPCantorCirculationHamiltonians`, no hypotheses, in `Smoothing/CMPPInstance.lean`. `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}` | UNCONDITIONAL |
| **R2** | Unconditional versions of the four `Main.lean` theorems on `Sphere4` (no `[HasTuringComplete…]`/`[HasCMPP…]` argument); old `*_of_cmpp` kept as corollaries | UNCONDITIONAL |
| **R3** | Gate 6 re-proved unconditionally in `CompChecks.lean`; `AUDIT.md` regenerated | UNCONDITIONAL |
| **R4 (interim)** | `theorem hasCMPP_of_simulator (S : UniversalReversibleSimulator) : HasCMPPCantorCirculationHamiltonians` | CONDITIONAL-ON-simulator S |
| **R5 (D2)** | **Poisson-Hamiltonian realization on S⁴**: there are finitely many `H̃ⱼ : Sphere4 → ℝ` (smooth) such that `d̄` equals the composition of the time-1 flows of the Hamiltonian vector fields of `s4AdaptedPoisson` for `H̃ⱼ`, and `IsTuringComplete ⇑d̄` | UNCONDITIONAL (statement finalized in Phase 0, §4.5) |

Frozen (no statement changes): `IsTuringComplete`, `TuringCompleteWitness`, `HaltsWithWindow`, `HasTuringCompleteAreaPreservingDiskIsotopy`,
`cantorDiskEmbed` and the generalized-shift definitions, all `Main.lean` conclusions.

---

## 2. Problem anatomy (verified in the repo and in the audit)

`HasCMPPCantorCirculationHamiltonians` has four fields: `sim : UniversalReversibleSimulator`, `r₀ ∈ (0,1)`,
`generators : List (CompactlySupportedPlanarHamiltonian r₀)`, and `realizes_shift`
(time-1 map of `listToDiskIsotopy generators` sends `cantorDiskEmbed enc s` to `cantorDiskEmbed enc (Φ.eval s)` for **all** `s : ℤ → A`).

Two independent missing halves:

| Half | Content | Status |
|---|---|---|
| **H2 smooth realization** | finite Hamiltonian list realizing the shift exactly on the Cantor set | Not started. Engine exists in `DiskSmoothing.lean` (flows, exact hyperbolic stretch on a ball, composition, area preservation) |
| **H1 universal reversible simulator** | one `ReversibleTM` + encoding simulating every `FinTM0` with windowed output, with primitive-recursive digit enumerators | **No `UniversalReversibleSimulator` exists anywhere.** `universalHaltingTM0` (M3.2) is an irreversible machine for one halting question, not a universal simulator |

Interface facts: `computable_approx` is per machine `M` (no uniformity in `M`), so `M ↦ table` may be noncomputable. `HaltsWithWindow` equivalence is halting-with-window, not step-exact.
`acceptBlocks` currently uses cylinders at one fixed radius `windowRadius M k`, which forces cell-faithful readout (see I2).

---

## 3. Reuse from `SympTopAutoForm` (gromov-genus0-compactness)

Checked by grep over its 57k lines: **no mathematical reuse** (no Moser, isotopy, Hamiltonian, shift or Cantor content; Mathlib 4.35, no TauCeti, so nothing can be imported). **High process reuse; port these:**

| Asset | Use here |
|---|---|
| `tests/PhaseAxiomCensus.lean` (`#phase_axiom_census`, `#audit_wiring`) | Gate G4: the final instance's transitive closure must contain the load-bearing lemmas (catches decorative `have`s) |
| `tests/CertificateSanity.lean` | Gate G5 satisfiability pattern for every new structure/hypothesis |
| Route-1 incident (`COMPLETION_PLAN.md`, 7 Nov) | A fake "unconditional" result forced all maps constant, making theorems vacuous. Source of the anti-vacuity gate |
| `tests/Adversarial*Challenger*.lean` | Verifiers write refutation attempts, not only confirmations |
| Labels *unconditional* / *certificate-parameterized* | Reused as the labels in §1 |
| `tools/build_bm25_index.py`, `premise_retrieval.py`, `extract_diffgeo_dataset.py`, `data/bm25_index.pkl` | Port to S4TP for retrieval (§6.3). Its corpora (`mathlib_v435_accepted_proofs.jsonl` 4000, `diffgeo_accepted_proofs.jsonl` 3330, `gemma_accepted_proofs.jsonl` 2670) are **Mathlib 4.35: stale names, syntax few-shot only** |
| `gemma-lean4:latest`, LoRA adapters | `gemma2:9b`-based, not portable to `gemma4:12B`. Syntax-scaffolding fallback only; **no fine-tuning in this mission** |

---

## 4. Mathematical route (Hamiltonian, Moser-free)

TauCeti has no Moser trick or embedded-disc isotopy extension (only Palais-style extension by the identity, Schoenflies, `Hamiltonian/{Quadratic,Hyperbolic,Localized,TimeDependent}`). The route below needs neither.

### 4.1 Lemma G0 (disjointness; removes the feared obstruction)
For a shift `Φ` on `D = {-1,0,1}` with `F(w) ∈ {-1,0,1}`: source rectangles `R_w` (`w ∈ A³`, size `B⁻²×B⁻¹`) are pairwise disjoint. The image of `R_w` is the full rectangle `R'_w` of the cylinder fixed at positions `D−F(w)`
(`B⁻¹×B⁻²` for `F=+1`; `B⁻³×1` for `F=−1`; `B⁻²×B⁻¹` for `F=0`).
**If `Φ.eval` is injective, the `R'_w` are pairwise disjoint** (a common point forces two compatible cylinders, hence a common configuration, hence `w = w'`; incompatible cylinders have disjoint closed intervals because middle-Cantor digits leave a gap).
Hence on `R_w`, `Φ` is exactly the affine area-preserving map `A_w(x,y) = (B^{F}x + aw, B^{−F}y + bw)`, with disjoint axis-parallel sources and targets.
(I re-derived `Φ(C_w)` and the positions `D−F` independently; they agree with the other draft. Signs of `F` against `Φ.eval`, and the fact that coordinate 0 carries the **negative** half, must be pinned in C0.)

### 4.2 Relocation Theorem (RT): the whole of H2
> Let `Pᵢ` (`i<n`) be pairwise-disjoint compact axis-parallel rectangles and `P'ᵢ = Aᵢ(Pᵢ)` pairwise disjoint, all in `ball 0 ρ`, with `Aᵢ = translation ∘ diag(λᵢ, λᵢ⁻¹)`, `λᵢ ∈ {B,1,1/B}`. Then there is a finite list of compactly supported planar **autonomous** Hamiltonians (support in `ball 0 r₀`) whose time-1 composite equals `Aᵢ` on `Pᵢ` for every `i`.

Architecture (every step is an exact rigid translation of one compact rectangle, or an exact in-place stretch):
1. **Sliding Lemma.** Sliding axis-parallel disjoint rectangles in `+x` in order of decreasing left edge is collision-free (a blocker overlapping in `y` is x-separated, so it has a larger left edge and moved earlier). First-moved goes farthest into its own parking slot.
2. **Evacuate sources** to slots.
3. **Workbench at the origin.** For each piece: lift to a corridor, travel, drop at the origin, apply the exact hyperbolic stretch (`bumpedHyperbolicStretchIsotopy`, `μ = log B`) for `F = ±1`, then move to its target-evacuation slot.
4. **Reverse sliding** brings pieces to `P'ᵢ` (targets are a disjoint family, so the same lemma applies backwards).

Only two primitives are needed: **L1** (new): exact rigid translation by `v` of a compact set `S`, identity outside a prescribed open `U ⊇ tube(S,v)` (a linear Hamiltonian times a cutoff `≡1` near the tube; generalizes `sectorSwapIsotopy`; reuses `timeDependentFlowOf_eq_of_hasMFDerivAt`); **L2** (exists): exact stretch on a closed ball.

**Design constraint from D2/R5:** all generators must be **autonomous** (`CompactlySupportedPlanarHamiltonian.ofAutonomous`). L1 (linear × cutoff) and L2 (bump × `xy`) already are. This is what makes R5 (§4.5) possible.

### 4.3 The room problem (decided by data, not assumed)
Today `cantorDiskEmbed` fills `(−1/2,1/2)²` of the unit disc, support radius `r₀<1`. The other draft claims there is no room to park `n = N³` pieces and proposes chart scale `c ≤ 1/(16N³)`. My own count disagrees in spirit: the free area outside the square is ≈ `π−1`, but some images are full-height strips (`B⁻³×1`) that only fit near the vertical axis. **Therefore C0 (numeric spike) must decide whether the current chart suffices.** Only if it provably does not, request I1 (§5) and obtain user sign-off (D3).

### 4.4 H1 route (largest uncertainty)
- **B1 Bennett reversibilization (generic).** Any `FinTM0` `U` gives a `ReversibleTM` `R_U` (history track): from `init'(c)` it reaches an accepting cylinder iff `U` halts; `stepPerm`/`dirIn` bijective.
- **B2 Universal `FinTM0` with windowed output.** One `U` such that for all `(M,t)`, `U` on `enc(M,t)` halts with an encoding of `M`'s final tape. **Blocked on `MISSION_DIRECTIVE_TMPARTREC.md`** (Mathlib proves partrec → TM only; the TM → partrec direction is formalized there as T-A/T-C, and the windowed universal TM0 as T-E(3)). B2 here reduces to transporting T-E(3) to `FinTM0`/`HaltsWithWindow` by relabeling. Under D2 there is no fixed-machine fallback.
- **B3 Assemble** into `UniversalReversibleSimulator` with primitive-recursive digit enumerators, using relaxed acceptance (I2).

### 4.5 R5: Poisson-Hamiltonian realization on S⁴ (new, from D2)
Goal: not merely "a Turing-complete diffeomorphism that happens to preserve π_f", but one **generated by π_f-Hamiltonian flows**.
Sketch (to be verified in Phase 0, question Q-P): `d̄(b,·) = ∏ᵢ φ^{ρ(b)}_{Hᵢ}` on the fibre, with autonomous `Hᵢ`, so `φ^{ρ(b)}_{Hᵢ} = φ¹_{ρ(b)Hᵢ}`. On a symplectic leaf (a fibre), the Hamiltonian field of `π_f` for `h̃` is leafwise: `X_h̃ = (density factor)·X_{h̃|leaf}` w.r.t. the leaf form, where the factor comes from the aligned volume's `c(b)>0` (`trivialization_pos_cooriented`). Take `H̃ᵢ = (ρ/c)·(Hᵢ ∘ chart⁻¹)`, extended by `0`. Compact support gives completeness of `X_{H̃ᵢ}`.
Must pin: the exact normalization `{g,h}_{π_f}Ω = dg∧dh∧f^*μ_Σ` vs `s4AlignedPositiveVolume`; that `bumpProfile`-slicing equals the time-1 flow; that flows commute properly across the region where `χ≢1`. If the autonomous trick fails, fall back to **time-dependent** Hamiltonians (still Hamiltonian flows; D1 satisfied).

### 4.6 Emergency appendix (only if sliding/relocation stalls, needs coordinator + user approval)
Parametric Moser route from my first draft: (T1) isotopy extension by compactly supported fields; (T2) collision-free motion of shrunken pieces with parking trick; (T3) compactly supported divergence lemma; (T4) parametric Moser correction; (T5) divergence-free compactly supported fields are Hamiltonian (primitive along a ray). Heavier (new Moser development) but keeps D1 via T5.

---

## 5. Permitted interface refactors (each needs verifier statement-diff review)

- **I1 (conditional, D3).** Similarity-rescale parameter `c` in `scaledCantorCoord`/`cantorDiskEmbed`, default recovering the current definition; no change to base, digits, or shift. Allowed **only if C0 proves necessity and the user signs off**. Existing lemma names preserved; root build + both `Checks` unchanged in meaning.
- **I2.** Accepting sets as arbitrary open unions of cylinder rectangles of any radius (still nonempty, depending only on `(M,k,w)`; `HaltsWithWindow` equivalence unchanged; `encodeOpen` unchanged). Removes the cell-faithful-readout burden from B2 without weakening universality.
- ~~I3 conjugacy bypass~~: **removed** (violates D1/D3).
Forbidden: touching `IsTuringComplete`, `TuringCompleteWitness`, `HaltsWithWindow`; strengthening any definition so a proof becomes easy (Route-1 incident).

---

## 6. Local-Model-First Engine (D4)

Facts measured: `gemma4:12B` (4-bit nvfp4, 7.7 GB, `num_ctx=32768`, `OLLAMA_NUM_PARALLEL=1`) runs at **≈7 tok/s** (92 tokens in 13.1 s on a trivial Lean goal). A 300-token proof ≈ 45 s plus a Lean check. Parallelism is capped at 1 by the RAM guardrail, so the gain is **frontier tokens and frontier wall-clock saved while the daemon works in the background**, not raw speed. Previous campaigns: S4TP 7 calls; gromov 499 calls with **no recorded outcomes**.

### 6.1 Division of labour
- Frontier (Carbon): architecture, **statements and `sorry` skeletons**, T2 core proofs, escalations, final integration.
- Local `gemma4:12B`: fills `sorry`s for T0/T1 via the compiler-in-the-loop prover; drafts T2 skeletons and premise lists.
- Argon (lint/docstring/import cleanup only, per `MISSION_DIRECTIVE.md` §2).

### 6.2 Tiers (rubric; thresholds set empirically in §6.5)
- **T0 algebra/combinatorics/boilerplate:** digit and geometric-series identities, interval/closed-interval disjointness, list/finset lemmas, slot ordering, `simp`/`ext`/API wrappers, instance plumbing, ≤100-col reflow.
- **T1 structured routine:** induction over Hamiltonian lists, `listToDiskIsotopy` composition lemmas, `ContDiff`/continuity of explicit formulas, compact-set/tube topology, TM step-simulation case analysis.
- **T2 core analysis/geometry:** flow exactness, Hamiltonian-field computations, pullback/Cartan, Bennett correctness architecture, partrec reasoning.

### 6.3 Tools (built in Wave 0, Python stdlib where possible; owner `@gemma-infra`)
1. `tools/gemma_loop.py`: **compiler-in-the-loop prover.** Input: declaration statement + module context. Prompt = system + top-8 retrieved premises + 3 retrieved accepted proofs + statement. Each candidate is written to `.agents/gemma_scratch/<decl>_<k>.lean`, checked with `LEAN_NUM_THREADS=2 lake env lean` (timeout 300 s), accepted iff exit 0 with no `sorry` and no warnings. On failure the first ≤30 error lines feed the next attempt. **≤5 attempts** (matches the 5-retry rule); attempts 4–5 enable thinking. Accepted proofs go to `.agents/gemma_accepted/<decl>.lean`. After 5 failures it writes `.agents/gemma_escalations/<decl>.json` (all attempts + errors), which Carbon reads, so frontier effort is not blind. Daemon/batch mode processes a queue of spec files in the background.
2. `tools/s4tp_index.py`: BM25 index over (a) this repo's declarations (signature + docstring), (b) Mathlib/TauCeti `v4.36` declarations from `.lake/packages` (regex of `theorem|lemma|def` + docstrings). Also builds `data/s4tp_accepted.jsonl` from our own ~19.5k verified lines (version-matched gold few-shot). Port of `build_bm25_index.py`/`premise_retrieval.py`.
3. `tools/gemma_bench.py`: calibration benchmark (§6.5).
4. Extended `tools/ollama_lean4_client.py`: `--with-premises`, outcome fields.

### 6.4 Ledger (fixes the gromov flaw)
Every record: `declaration`, `tier`, `attempt`, `accepted` (verified by Lean, never self-reported), `error_class`, `tokens`, `latency_ms`, `lean_ms`. `ledger-summary` reports acceptance per tier and per milestone.

### 6.5 Calibration before routing (gate GM1)
Take ≥40 already-proved lemmas from this repo stratified over T0/T1/T2, hide the proofs, **exclude them and near duplicates from the retrieval index**, run the loop, report pass@1/pass@5 and wall time per tier to `docs/cmpp/gemma_calibration.md`.
Routing rule (set by data, not hope): tier is **gemma-first** if pass@5 ≥ 30%; **gemma-draft-only** if 10–30%; **frontier** if < 10%. I do not assume 12B can do analysis; the pipeline is built so that failure costs little.

### 6.6 Slot accounting (24 GB guardrail)
Max 2 active Lean processes. The gemma daemon's `lake env lean` checks use **one slot**; at most **one frontier Lean worker** uses the other. Steady state: daemon + 1 frontier worker. The A-chain and B-chain therefore alternate on the frontier slot rather than run as two frontier workers.
Wall-clock estimate to be refreshed after GM1: ≈ (45 s generation + Lean check) × (≈2–3 attempts) per declaration; 100 declarations ≈ 4–6 h in the background.

### 6.7 Provenance enforcement (gate G8)
`tools/check_gemma_provenance.py` lists every T0/T1 declaration added in a milestone diff and requires **either** a file in `.agents/gemma_accepted/` **or** an escalation file with **5 logged failed attempts**. A frontier-written T0/T1 proof without that record fails the gate. Milestone reports must state counts by origin (gemma-accepted / escalated-then-frontier / frontier) and the per-tier acceptance rate.

---

## 7. Milestones, ownership, waves

Conventions: new files under `S4TuringPoisson/Smoothing/CMPP/` unless stated; exclusive ownership; every milestone ends with the §8 gates; merge `--no-ff` only after both verifiers pass.

| ID | Milestone | Owner / files | Done when |
|---|---|---|---|
| **C0** | **Python spike, no Lean.** `tools/cmpp_planner.py`: toy `N=2,3` (`B=3,5`), random injective shift; generate rectangles, check G0, run the 4-step pipeline numerically, verify the composite reproduces `Φ` on random Cantor points, **decide the room question (§4.3)**, pin signs and slot coordinates, pin the R5 normalization numerically. Output `docs/cmpp/geometry_spec.md` | `@planner` (light) | exact on 10⁴ random points; I1 needed or not decided with evidence |
| **GI** | Gemma infra §6.3 + census port (`#audit_wiring`) | `@gemma-infra` (Argon): `tools/`, `tests/` | tools run end to end on a toy lemma; ledger records `accepted` |
| **GM1** | Calibration benchmark and routing | `@gemma-infra` | `docs/cmpp/gemma_calibration.md` + `docs/cmpp/routing.md` |
| **A0** | Chart scale I1 (**only if C0 says so and user approves**) | `@chart`: `Dynamics/GeneralizedShift.lean` | root `--wfail` green, `Checks` unchanged in meaning |
| **A1** | Digit algebra: `cantorCoord` under head replacement/shift; cylinder rectangle = interval product; **G0**; `A_w` formulas | `@digits`: `CMPP/Digits.lean` (T0-heavy: gemma-first) | `A_w(R_w)=R'_w`; `A_w(cantorDiskEmbed s) = cantorDiskEmbed (Φ.eval s)` on `cyl w` |
| **A2** | L1 (compact-set rigid translation, autonomous) + L2 wrapper | `@flows`: `CMPP/Primitives.lean` (T2: Carbon, gemma drafts) | exact on `S`, identity off `U`, area-preserving, compact support |
| **A3** | Sliding Lemma, slot permutation, **RT** (abstract rectangles) | `@relocate`: `CMPP/Relocation.lean` | RT generic in `n`, 0 `sorry` |
| **A4** | `RealizesGeneralizedShiftByHamiltonians` for every injective `shiftDom3` shift; **R4** | `@assemble`: `CMPP/Realize.lean` | R4 delivered |
| **B1** | Bennett reversibilization | `@bennett`: `Dynamics/Reversible/Bennett.lean` | orbit/accept equivalence + bijectivity |
| **B2** | Universal `FinTM0`, TM → partrec lemma | `@universal`: `Dynamics/Reversible/Universal.lean` | simulation theorem for all `(M,t)` |
| **B3** | Refactor I2; construct `UniversalReversibleSimulator` | `@simulator`: `CMPP/Simulator.lean` | inhabited, primrec digits |
| **P** | **R5 Poisson-Hamiltonian realization** on S⁴ (Q-P resolved in C0) | `@poisson-ham`: `Extension/PoissonHamiltonian.lean` | statement of §4.5 proved for the final generators |
| **Z** | Final instance, R1–R3, ported `#audit_wiring`, `AUDIT.md` | `@leaf-final` | all gates |

Waves: **W0** = C0 ‖ GI (Python, negligible RAM) → GM1 (one Lean slot). **W1** = A0 (if approved), A1 (daemon-first). **W2** = A2, then A3, A4 (frontier slot) with the daemon filling T0/T1 `sorry`s. **W3** = B1, B2, B3 (frontier slot alternates with A-chain). **W4** = P, Z. Verifiers `@verifier-geom` (A-chain, P) and `@verifier-comp` (B-chain) stay parked until a milestone lands and must **attempt refutations**.

Effort (honest): comparable to the previous campaign (10-25k lines). The A-chain is bounded and understood; **the B-chain, especially B2, is the dominant risk**.

---

## 8. Verification gates (a milestone cannot merge unless all apply and pass)

- **G1 Build.** `LEAN_NUM_THREADS=2 lake build --wfail`: 0 errors/warnings, ≤100 columns.
- **G2 Axioms.** `collectAxioms` over every new declaration ⊆ `{propext, Classical.choice, Quot.sound}`; comment-stripped scan finds none of `sorry|admit|axiom|unsafe|implemented_by|native_decide|opaque|maxHeartbeats`.
- **G3 Statement freeze.** `git diff` shows no change to frozen statements (§1); I1/I2 reviewed line by line.
- **G4 Wiring audit.** The final instance's transitive closure contains `toDiskIsotopy`, L1, L2, the Sliding Lemma, G0 and `ReversibleTM.bijective_eval`.
- **G5 Anti-vacuity / satisfiability** (`CertificateSanity` pattern). For every new structure/hypothesis, a sanity file exhibits an inhabitant or proves non-contradiction. Required toy end-to-end test: realize a concrete 2-3 symbol reversible machine's shift (reuse `R_flipRight_shift` from `CompChecks`) through the pipeline and check exactness at specific Cantor points.
- **G6 Regression.** Existing `GeomChecks`/`CompChecks` pass; `*_of_cmpp` theorems still hold.
- **G7 Honest labelling.** Every deliverable is UNCONDITIONAL or CONDITIONAL-ON-<named object>. No relabelling by weakening.
- **G8 Local-model provenance** (§6.7) and the ledger report (§6.4).
- **G9 Final.** R1–R3 and R5 hold; `AUDIT.md` regenerated with Gap 1 closed or reduced to a named residual.

---

## 9. Risks, kill criteria

| Risk | Mitigation |
|---|---|
| H1 larger than H2 | Ship **R4** as an interim CONDITIONAL checkpoint; continue B-chain. **No fixed-machine fallback (D2)** |
| 12B model weak on Lean analysis | Calibrate first (GM1); T2 stays frontier; failure costs only background time. Ledger documents the real success rate |
| Room problem (§4.3) | Decided by C0 data; I1 only with user sign-off (D3) |
| `Real.ofDigits` algebra (A1) | Daemon-first; formulas validated numerically in C0 |
| Flow exactness off balls (A2) | Reuse `timeDependentFlowOf_eq_of_hasMFDerivAt` pattern; smooth Urysohn cutoffs on compact tubes |
| R5 normalization mismatch | Resolve in C0; fall back to time-dependent Hamiltonians |
| TM → partrec absent in Mathlib (B2) | Budget explicitly; escalate to the user, not to a weaker theorem |
| Vacuity temptation | G5, G7, refutation-seeking verifiers |
| RAM pressure | Daemon + 1 frontier worker; `workflow_control.py pause` |

Kill criterion: if a milestone exceeds 3x its estimate with no green gate, the coordinator **pauses, records the blocker, and consults the user** (no automatic weakening of the target).

---

## 10. Lean statement sketches (adapt to actual names)

```lean
theorem exists_translation_hamiltonian {S : Set EuclideanPlane} (hS : IsCompact S) (v : EuclideanPlane)
    {U : Set EuclideanPlane} (hU : IsOpen U) (htube : tube S v ⊆ U) (hr : U ⊆ Metric.ball 0 r₀) :
    ∃ P : CompactlySupportedPlanarHamiltonian r₀, P.IsAutonomous ∧
      (∀ y ∈ S, P.toDiskIsotopy.diskTimeOneMap y = y + v) ∧
      (∀ y ∉ U, P.toDiskIsotopy.diskTimeOneMap y = y)

theorem image_rects_disjoint {Φ : GeneralizedShift A} (hinj : Function.Injective Φ.eval) ... :
    Pairwise (Disjoint on fun w => imageRect Φ w)

theorem relocation (P : Fin n → Set EuclideanPlane) (A : Fin n → AffineMap) ... :
    ∃ Ps : List (CompactlySupportedPlanarHamiltonian r₀), (∀ H ∈ Ps, H.IsAutonomous) ∧
      ∀ i, ∀ y ∈ P i, (listToDiskIsotopy hr₀ Ps).diskTimeOneMap y = A i y

theorem hasCMPP_of_simulator (S : UniversalReversibleSimulator) : HasCMPPCantorCirculationHamiltonians

-- R5 (final form fixed in C0)
theorem exists_poisson_hamiltonian_realization_S4 :
    ∃ Hs : List (Sphere4 → ℝ), (∀ H ∈ Hs, ContMDiff (𝓡 4) 𝓘(ℝ) ∞ H) ∧
      ∃ d_bar : Sphere4 ≃ₘ⟮𝓡 4, 𝓡 4⟯ Sphere4,
        d_bar = composeTimeOneFlows s4AdaptedPoisson Hs ∧ IsTuringComplete ⇑d_bar
```

---

## 11. References
CMPP21 (Cardona-Miranda-Peralta-Salas-Presas, PNAS 2021, arXiv:2012.12828) §4-5, Thm 5.2; Moore 1990; Bennett 1973; Lecerf 1963; Morita (small universal reversible TMs); Guibas-Yao (translating sets of rectangles); Moser 1965 and Dacorogna-Moser 1990 (appendix only); Palais 1960 / Hirsch Ch. 8 (not needed by the main route).

## 12. Immediate next action
**Prerequisite:** `MISSION_DIRECTIVE_TMPARTREC.md` runs first. Its W0 builds the local-model engine (GI/GM1 here reuse it, recalibrated on CMPP-style lemmas), and its T-C/T-E deliver what B2 needs.
Then launch **W0** here: C0 (Python spike) in parallel with GI adaptation, then GM1. Do not start any frontier Lean worker before `docs/cmpp/routing.md` exists. The A-chain (geometry) does not depend on TM→Partrec and may start once the engine exists.
