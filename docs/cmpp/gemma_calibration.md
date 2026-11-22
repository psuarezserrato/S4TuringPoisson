# CMPP Milestone GM1: Stratified 40-Lemma Calibration Report for Local `gemma4:12B`

- **Repository**: `/Users/pablosuarez/Desktop/S4TuringPoisson` (Lean `v4.36.0`, Mathlib + TauCeti `v4.36.0`, `TuringRecursive` linked)
- **Model & Runner**: Local `gemma4:12B` (4-bit `nvfp4` MLX via headless Ollama `0.40.16` at `http://localhost:11434/api/chat`)
- **Benchmark Harness**: `tools/gemma_bench.py` driving `tools/gemma_loop.py`, `tools/s4tp_index.py`, and `tools/ledger.py`
- **Verification Standard**: `LEAN_NUM_THREADS=2 lake env lean` exit code `0`, `0` warnings, `0` errors, `0` forbidden tokens (`sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `native_decide`), declaration header before `:=` byte-for-byte identical, target declaration and near-duplicates excluded from BM25 retrieval (`--exclude`) and stripped of `@[simp]` (`attribute [-simp]`).

---

## 1. Hardware, Anti-Leak & 24 GB Unified RAM Configuration

Following the hardware validation lessons from `Turing-recursive`, the local prover engine (`config/ollama_gemma_config.json`, `tools/ollama_lean4_client.py`, `tools/gemma_loop.py`) locks:

| Parameter | Locked Value | Rationale |
|---|---|---|
| `primary_model` | `gemma4:12B` | Local 12B 4-bit MLX runner (~7.7 GB active weights) |
| `keep_alive` | `0` (numeric) | Forces Ollama to unload `gemma4:12B` from unified RAM immediately after each HTTP `/api/chat` response (`0 GB` idle between calls), preventing MLX Metal memory leaks and ensuring `ollama` and `lake env lean` never coexist in RAM |
| `num_ctx` | `4096` | Bounds KV-cache footprint on 24 GB unified memory |
| `max_prompt_chars` | `4000` | Prevents context window overflow and prompt-truncation stalls |
| `think` | `False` (all 5 attempts) | Thinking mode wastes ~80 s and frequently exhausts `num_predict` before emitting code |
| `num_predict` | `384` (attempts 1–3), `512` (attempts 4–5) | Sufficient for T0/T1 tactic proofs while capping runaway generation latency |
| `temperature` / `top_p` / `top_k` | `1.0` / `0.95` / `64` | Diverse multi-attempt sampling across the 5-retry budget |
| `BM25 retrieval` | `top_k = 4` premises, `top_k = 1` accepted proof | Indexed over **50,851 premises** and **5,757 accepted proofs** (`S4TuringPoisson` + `TuringRecursive` + `TauCeti` + `Mathlib`) with compound-identifier tokenization and `1.35x` project / `1.25x` definition-unfolding boosts |
| `Concurrency` | `1` sequential Lean slot (`LEAN_NUM_THREADS=2`) | Strictly sequential execution (`ollama` generation $\to$ model unload $\to$ `lake env lean` verification) |

### Swap & Unified Memory Telemetry Across the 40-Lemma Run

- **Gold proof pre-verification (`python3 tools/gemma_bench.py --verify-gold`)**: All **40/40** reference proofs compiled in a single Lean check in **3,440 ms** (`0` warnings, `0` errors).
- **`ollama ps` verification after every chunk**: **0 resident runners** (`NAME ID SIZE PROCESSOR CONTEXT RUNNER UNTIL` empty after every chunk), confirming `"keep_alive": 0` unloads the 7.7 GB MLX runner immediately after each generation.
- **`sysctl vm.swapusage` trajectory**:
  - Pre-Chunk 1 baseline (with IDE language servers active): `used = 5637.38M` (`5.51 GB`)
  - Peak during Chunk 1 (`T0_01`–`T0_08`, before macOS reclaimed cold IDE pages): `used = 7012.25M` (`6.85 GB`)
  - Chunks 2–5 (`T0_09`–`T2_10`): stayed steadily between **`3560.88M` (`3.48 GB`)** and **`5028.94M` (`4.91 GB`)**
  - Final post-GM1 `sysctl vm.swapusage`: `total = 5120.00M  used = 3921.88M  free = 1198.12M` (**1.71 GB lower** than the starting baseline).

---

## 2. Aggregate Calibration Results by Tier

Per `MISSION_DIRECTIVE_CMPP.md` §6.5, the 40 already-proved lemmas from `S4TuringPoisson/Dynamics/GeneralizedShift.lean` and `S4TuringPoisson/Smoothing/DiskSmoothing.lean` were stratified into:
- **Tier T0 (15 lemmas)**: algebra, combinatorics, boilerplate, `shiftSeq`/`replaceDom`/`restrictDom` identities, `shiftDom3` membership, `cantorBase` bounds, and `cantorCoord` range wrappers.
- **Tier T1 (15 lemmas)**: structured routine proofs — `ReversibleTM`/`FinTM0` multi-step orbit induction, `listComp`/`listToDiskIsotopy` fold/append induction, `ContDiff`/continuity of explicit coordinate formulas, and `AreaPreservingDiskIsotopy` slice/ball properties.
- **Tier T2 (10 lemmas)**: core analysis, geometry, Cantor digit arithmetic (`cantorPrefixCode_add_one_le_pow`, `sum_ofDigitsTerm_cantorEvenDigit`, `scaledCantorCoord_injective`), `Primrec` fold combinators, Euclidean norm/ball geometry, and `bumpedHyperbolicStretchIsotopy` time-1 evaluation.

| Tier | Lemmas ($n$) | `pass@1` | `pass@5` | Total Calls | Mean Wall / Decl | Mean Tokens / Decl | Mean Tokens / Call | Mean Model Latency / Call | Mean Lean Check / Call | Routing Rule (§6.5) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| **T0** | 15 | **5 / 15 (33.3%)** | **8 / 15 (53.3%)** | 46 | 111.1 s | 467.9 | 152.6 | 25,803.3 ms | 10,331.5 ms | **`gemma-first`** ($\ge 30\%$) |
| **T1** | 15 | **0 / 15 (0.0%)** | **0 / 15 (0.0%)** | 75 | 260.4 s | 1,406.9 | 281.4 | 41,685.1 ms | 10,304.1 ms | **`frontier`** ($< 10\%$) |
| **T2** | 10 | **0 / 10 (0.0%)** | **0 / 10 (0.0%)** | 50 | 307.5 s | 1,704.5 | 340.9 | 49,461.0 ms | 11,940.2 ms | **`frontier`** ($< 10\%$) |
| **Overall** | **40** | **5 / 40 (12.5%)** | **8 / 40 (20.0%)** | **171** | **216.2 s** | **1,129.2** | **264.1** | **39,686.4 ms** | **10,789.8 ms** | **T0 `gemma-first`; T1/T2 `frontier`** |

Total benchmark wall time across all 171 compiler-verified attempts: **8,647.1 s** (`2.40 hours`), **45,167 generated tokens**.

---

## 3. Error-Class Distribution Across All 171 Verified Attempts

Every candidate was checked by `LEAN_NUM_THREADS=2 lake env lean` (and pre-screened for statement preservation and forbidden tokens) and classified by `tools/ledger.py`:

| Error Class | T0 Calls (46) | T1 Calls (75) | T2 Calls (50) | All Calls (171) | Share (%) |
|---|---:|---:|---:|---:|---:|
| `none` (Compiler-Verified Accepted) | **8** | 0 | 0 | **8** | **4.7%** |
| `other` (tactic failure / `omega` / `simp` / `rw` failed) | 14 | 24 | 10 | 48 | 28.1% |
| `unsolved goals` | 7 | 16 | 19 | 42 | 24.6% |
| `unknown identifier` | 8 | 18 | 8 | 34 | 19.9% |
| `syntax` (Lean 4 parser / splice rejection) | 3 | 12 | 7 | 22 | 12.9% |
| `type mismatch` | 6 | 5 | 6 | 17 | 9.9% |
| `timeout` | 0 | 0 | 0 | 0 | 0.0% |

Key observations from the error distribution:
1. **Zero Lean compiler timeouts (`0 / 171`)**: Every generated candidate was verified by `lake env lean` in ~10.8 s mean (~3.4 s–12.1 s depending on imports).
2. **Compiler feedback loop (`attempt 1` $\to$ `attempt 2`) lifted T0 acceptance from `33.3%` to `53.3%`**: Three T0 declarations that failed on Attempt 1 (`T0_03` `replaceDom_mem`, `T0_06` `GeneralizedShift.ofTwoDomains_D_self`, and `T0_10` `tape_write_write`) succeeded on **Attempt 2** after `gemma_loop.py` fed back the first $\le 12$ compiler error lines.

---

## 4. Per-Declaration Results Table (40 Stratified Lemmas)

### 4.1 Tier T0 (15 Lemmas — `pass@1 = 33.3%`, `pass@5 = 53.3%`)

| ID | `S4TuringPoisson` Declaration | Outcome | Attempts | Wall (s) | Tokens | Accepted Proof / Error Sequence |
|---|---|---|---:|---:|---:|---|
| `T0_01` | `shiftSeq_zero` | **PASS@1** | 1 | 32.2 | 43 | `by ext k; simp` |
| `T0_02` | `shiftSeq_add` | FAIL(5) | 5 | 148.4 | 377 | `['other', 'unsolved goals', 'other', 'other', 'unsolved goals']` |
| `T0_03` | `replaceDom_mem` | **PASS@2** | 2 | 58.1 | 165 | `by unfold replaceDom; simp [hk]` |
| `T0_04` | `replaceDom_notMem` | **PASS@1** | 1 | 23.8 | 82 | `by unfold replaceDom; simp [hk]` |
| `T0_05` | `restrictDom_replaceDom` | FAIL(5) | 5 | 148.9 | 400 | `['other', 'other', 'other', 'other', 'other']` |
| `T0_06` | `GeneralizedShift.ofTwoDomains_D_self` | **PASS@2** | 2 | 66.6 | 177 | `by unfold GeneralizedShift.ofTwoDomains; simp` |
| `T0_07` | `mem_shiftDom3_iff` | FAIL(5) | 5 | 177.7 | 655 | `['other', 'syntax', 'type mismatch', 'unknown identifier', 'unknown identifier']` |
| `T0_08` | `notMem_shiftDom3_iff` | FAIL(5) | 5 | 181.7 | 907 | `['other', 'unknown identifier', 'unsolved goals', 'unknown identifier', 'unknown identifier']` |
| `T0_09` | `mkDom3_eta` | FAIL(5) | 5 | 170.6 | 578 | `['unsolved goals', 'other', 'syntax', 'unsolved goals', 'syntax']` |
| `T0_10` | `tape_write_write` | **PASS@2** | 2 | 60.6 | 120 | `rfl` |
| `T0_11` | `cantorBase_eq_of_two_le` | **PASS@1** | 1 | 30.2 | 58 | `by unfold cantorBase; omega` |
| `T0_12` | `three_le_cantorBase` | **PASS@1** | 1 | 31.5 | 40 | `by unfold cantorBase; omega` |
| `T0_13` | `cantorBase_pos` | **PASS@1** | 1 | 33.5 | 38 | `by unfold cantorBase; omega` |
| `T0_14` | `cantorCoord_nonneg` | FAIL(5) | 5 | 242.8 | 1,374 | `['other', 'unknown identifier', 'type mismatch', 'other', 'unknown identifier']` |
| `T0_15` | `cantorCoord_le_one` | FAIL(5) | 5 | 260.2 | 2,004 | `['unsolved goals', 'type mismatch', 'type mismatch', 'type mismatch', 'type mismatch']` |

### 4.2 Tier T1 (15 Lemmas — `pass@1 = 0.0%`, `pass@5 = 0.0%`)

| ID | `S4TuringPoisson` Declaration | Outcome | Attempts | Wall (s) | Tokens | Error Sequence |
|---|---|---|---:|---:|---:|---|
| `T1_01` | `ReversibleTM.iterate_eval_encodeCfg` | FAIL(5) | 5 | 191.0 | 806 | `['other', 'unknown identifier', 'unknown identifier', 'unknown identifier', 'unknown identifier']` |
| `T1_02` | `FinTM0.iterate_eval_encodeHaltedTape` | FAIL(5) | 5 | 175.5 | 636 | `['other', 'other', 'unknown identifier', 'other', 'other']` |
| `T1_03` | `FinTM0.encodeActiveCfg_notMem_haltCylinder` | FAIL(5) | 5 | 330.2 | 2,176 | `['type mismatch', 'unsolved goals', 'unsolved goals', 'type mismatch', 'unsolved goals']` |
| `T1_04` | `FinTM0.encodeHaltedTape_mem_haltCylinder_iff` | FAIL(5) | 5 | 269.6 | 1,216 | `['syntax', 'syntax', 'syntax', 'syntax', 'syntax']` |
| `T1_05` | `continuous_scaledCantorCoord` | FAIL(5) | 5 | 357.4 | 2,176 | `['type mismatch', 'other', 'other', 'type mismatch', 'other']` |
| `T1_06` | `scaledCantorCoord_mem_Icc` | FAIL(5) | 5 | 162.1 | 380 | `['unsolved goals', 'unsolved goals', 'unsolved goals', 'unsolved goals', 'unsolved goals']` |
| `T1_07` | `cantorOpenInterval_nonempty` | FAIL(5) | 5 | 308.9 | 1,695 | `['other', 'unknown identifier', 'unknown identifier', 'unknown identifier', 'unknown identifier']` |
| `T1_08` | `continuous_negHalf` | FAIL(5) | 5 | 303.3 | 1,637 | `['unsolved goals', 'unsolved goals', 'unknown identifier', 'unsolved goals', 'unknown identifier']` |
| `T1_09` | `AreaPreservingDiskIsotopy.contDiff_slice` | FAIL(5) | 5 | 263.3 | 1,199 | `['other', 'unknown identifier', 'unknown identifier', 'other', 'unknown identifier']` |
| `T1_10` | `AreaPreservingDiskIsotopy.dInv_eq_self_of_notMem_ball` | FAIL(5) | 5 | 220.8 | 1,001 | `['other', 'other', 'other', 'other', 'other']` |
| `T1_11` | `AreaPreservingDiskIsotopy.dInv_time_zero` | FAIL(5) | 5 | 268.9 | 1,604 | `['other', 'other', 'other', 'unsolved goals', 'type mismatch']` |
| `T1_12` | `AreaPreservingDiskIsotopy.listComp_diskTimeOneMap` | FAIL(5) | 5 | 203.8 | 761 | `['syntax', 'syntax', 'syntax', 'syntax', 'syntax']` |
| `T1_13` | `listToDiskIsotopy_append_diskTimeOneMap` | FAIL(5) | 5 | 278.8 | 2,053 | `['other', 'other', 'unsolved goals', 'unsolved goals', 'syntax']` |
| `T1_14` | `RealizesGeneralizedShiftByHamiltonians.append` | FAIL(5) | 5 | 301.4 | 2,127 | `['syntax', 'other', 'unsolved goals', 'unknown identifier', 'unsolved goals']` |
| `T1_15` | `contDiff_rotQuad` | FAIL(5) | 5 | 271.0 | 1,637 | `['unknown identifier', 'unknown identifier', 'other', 'unknown identifier', 'other']` |

### 4.3 Tier T2 (10 Lemmas — `pass@1 = 0.0%`, `pass@5 = 0.0%`)

| ID | `S4TuringPoisson` Declaration | Outcome | Attempts | Wall (s) | Tokens | Error Sequence |
|---|---|---|---:|---:|---:|---|
| `T2_01` | `GeneralizedShift.eval_ofTwoDomains` | FAIL(5) | 5 | 312.5 | 2,176 | `['unsolved goals', 'type mismatch', 'type mismatch', 'type mismatch', 'unsolved goals']` |
| `T2_02` | `ReversibleTM.invStep_step` | FAIL(5) | 5 | 310.0 | 1,708 | `['unknown identifier', 'unknown identifier', 'unknown identifier', 'unknown identifier', 'type mismatch']` |
| `T2_03` | `cantorPrefixCode_add_one_le_pow` | FAIL(5) | 5 | 353.5 | 2,142 | `['unsolved goals', 'unsolved goals', 'unsolved goals', 'unsolved goals', 'unsolved goals']` |
| `T2_04` | `sum_ofDigitsTerm_cantorEvenDigit` | FAIL(5) | 5 | 333.6 | 2,176 | `['other', 'other', 'other', 'syntax', 'other']` |
| `T2_05` | `scaledCantorCoord_injective` | FAIL(5) | 5 | 238.9 | 1,125 | `['other', 'other', 'syntax', 'other', 'type mismatch']` |
| `T2_06` | `cantorPrefixPairList_snd` | FAIL(5) | 5 | 180.2 | 516 | `['syntax', 'syntax', 'syntax', 'syntax', 'syntax']` |
| `T2_07` | `primrec_approxCantorList` | FAIL(5) | 5 | 279.2 | 1,355 | `['unsolved goals', 'unsolved goals', 'unsolved goals', 'other', 'unknown identifier']` |
| `T2_08` | `norm_planeRotate` | FAIL(5) | 5 | 277.2 | 1,495 | `['other', 'type mismatch', 'unsolved goals', 'unsolved goals', 'unknown identifier']` |
| `T2_09` | `disjoint_symmetric_closedBalls` | FAIL(5) | 5 | 391.8 | 2,176 | `['unsolved goals', 'unsolved goals', 'unsolved goals', 'unsolved goals', 'other']` |
| `T2_10` | `bumpedHyperbolicStretchIsotopy_cantorBase_timeOne` | FAIL(5) | 5 | 397.7 | 2,176 | `['unknown identifier', 'unsolved goals', 'unsolved goals', 'unsolved goals', 'unknown identifier']` |

---

## 5. Qualitative Analysis: Where `gemma4:12B` Excels vs. Escalates

1. **Where `gemma4:12B` Excels (T0 Sub-categories — `53.3%` `pass@5`, `100%` on `cantorBase` / `replaceDom`)**:
   - **Definition-unfolding + `omega` arithmetic (`T0_11`, `T0_12`, `T0_13` — 3/3 = 100% `pass@1`)**: When `tools/s4tp_index.py` retrieves the underlying `def` (e.g., `def cantorBase (N : ℕ) : ℕ := max (2 * N - 1) 3`), `gemma4:12B` reliably emits `by unfold cantorBase; omega` on Attempt 1 in ~31 s.
   - **Definition-unfolding + `simp` / `ext` / `rfl` (`T0_01`, `T0_03`, `T0_04`, `T0_06`, `T0_10` — 5/6 = 83.3% `pass@5`)**: For `shiftSeq_zero`, `replaceDom_mem`, `replaceDom_notMem`, `GeneralizedShift.ofTwoDomains_D_self`, and `tape_write_write`, `gemma4:12B` either succeeds on Attempt 1 (`by ext k; simp`, `by unfold replaceDom; simp [hk]`) or uses the Attempt 1 compiler diagnostic to switch to `unfold ...; simp` or `rfl` on Attempt 2.
2. **Where `gemma4:12B` Escalates (T1 & T2 — `0.0%` `pass@5`)**:
   - **Mathlib v4.36 API hallucination (`unknown identifier`, 19.9% of calls)**: On `Real.ofDigits` (`T0_14`, `T0_15`), `ContDiff` (`T1_09`, `T1_15`), and `Metric.closedBall` (`T2_09`), `gemma4:12B` frequently guesses Lean 3 / Mathlib 4.35 names (e.g., `Real.ofDigits_nonneg` with explicit arguments or non-existent `ContDiff.prod_mk` variants).
   - **Structured induction & `calc` chains (`T1_01`, `T1_10`–`T1_14`, `T2_03`–`T2_06`)**: In Lean 4 `induction ... with | nil => ... | cons ... => ...` or dependent `Fin` induction, `gemma4:12B` often drops an implicit binder, uses Lean 3 `induction'` syntax without importing `Mathlib.Tactic.Induction`, or leaves trailing subgoals (`unsolved goals`, 24.6% of calls).
   - **Value of `.agents/gemma_escalations/<decl>.json`**: Even when a T0 declaration fails 5 attempts, `gemma_loop.py` logs the top-4 retrieved BM25 premises and all 5 compiler error diagnostics to `.agents/gemma_escalations/<decl>.json` so the frontier worker (Gemini 4 Carbon) can discharge the escalated lemma in one pass.
