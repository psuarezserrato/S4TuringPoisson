#!/usr/bin/env python3
"""
tools/gemma_bench.py — GM1 Stratified 40-Lemma Calibration Benchmark for gemma4:12B in S4TuringPoisson

Evaluates `tools/gemma_loop.py` on 40 already-proved lemmas from `S4TuringPoisson` across:
  - 15 T0 (algebra / combinatorics / boilerplate: shiftSeq, replaceDom, shiftDom3, cantorBase, cantorCoord bounds)
  - 15 T1 (structured routine: listToDiskIsotopy induction, ContDiff/continuity of explicit formulas,
           interval/ball properties, TM step simulation)
  - 10 T2 (core analysis / geometry / Cantor / Primrec: prefix codes, ofDigits sums, scaledCantorCoord
           injectivity, planeRotate norm, disjoint balls, hyperbolic stretch, primrec_approxCantorList)

Target declarations and near-duplicates are excluded from BM25 premise/proof retrieval AND
forbidden from being invoked directly or via `@[simp]` in candidate proofs.
"""

import argparse
import json
import os
import sys
import tempfile
import time
from pathlib import Path
from typing import Any, Dict, List, Optional

TOOLS_DIR = Path(__file__).resolve().parent
if str(TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(TOOLS_DIR))

import gemma_loop
import s4tp_index as bm25_index
import ledger
import workflow_control

COMMON_PREAMBLE = """import S4TuringPoisson.Dynamics.GeneralizedShift
import S4TuringPoisson.Smoothing.DiskSmoothing

open Bundle Filter Function Metric Module Set TopologicalSpace
open scoped ContDiff Manifold Topology
open S4TuringPoisson
"""

CALIBRATION_BENCHMARK: List[Dict[str, Any]] = [
    # =========================================================================
    # TIER T0 (15 lemmas): algebra / combinatorics / boilerplate / simp / ext
    # =========================================================================
    {
        "id": "T0_01",
        "tier": "T0",
        "s4tp_name": "S4TuringPoisson.shiftSeq_zero",
        "spec_name": "cal_shiftSeq_zero",
        "exclude": ["S4TuringPoisson.shiftSeq_zero", "shiftSeq_zero"],
        "unsSimp": ["S4TuringPoisson.shiftSeq_zero"],
        "statement": "theorem cal_shiftSeq_zero {A : Type*} (s : ℤ → A) : shiftSeq 0 s = s",
        "gold_proof": "by\n  funext k\n  simp [shiftSeq]",
    },
    {
        "id": "T0_02",
        "tier": "T0",
        "s4tp_name": "S4TuringPoisson.shiftSeq_add",
        "spec_name": "cal_shiftSeq_add",
        "exclude": ["S4TuringPoisson.shiftSeq_add", "shiftSeq_add"],
        "unsSimp": [],
        "statement": (
            "theorem cal_shiftSeq_add {A : Type*} (m₁ m₂ : ℤ) (s : ℤ → A) :\n"
            "    shiftSeq m₁ (shiftSeq m₂ s) = shiftSeq (m₁ + m₂) s"
        ),
        "gold_proof": "by\n  funext k\n  simp [shiftSeq, add_assoc]",
    },
    {
        "id": "T0_03",
        "tier": "T0",
        "s4tp_name": "S4TuringPoisson.replaceDom_mem",
        "spec_name": "cal_replaceDom_mem",
        "exclude": ["S4TuringPoisson.replaceDom_mem", "replaceDom_mem"],
        "unsSimp": ["S4TuringPoisson.replaceDom_mem"],
        "statement": (
            "theorem cal_replaceDom_mem {A : Type*} (D : Finset ℤ) (w : D → A) (s : ℤ → A) {k : ℤ}\n"
            "    (hk : k ∈ D) : replaceDom D w s k = w ⟨k, hk⟩"
        ),
        "gold_proof": "by\n  simp [replaceDom, hk]",
    },
    {
        "id": "T0_04",
        "tier": "T0",
        "s4tp_name": "S4TuringPoisson.replaceDom_notMem",
        "spec_name": "cal_replaceDom_notMem",
        "exclude": ["S4TuringPoisson.replaceDom_notMem", "replaceDom_notMem"],
        "unsSimp": ["S4TuringPoisson.replaceDom_notMem"],
        "statement": (
            "theorem cal_replaceDom_notMem {A : Type*} (D : Finset ℤ) (w : D → A) (s : ℤ → A) {k : ℤ}\n"
            "    (hk : k ∉ D) : replaceDom D w s k = s k"
        ),
        "gold_proof": "by\n  simp [replaceDom, hk]",
    },
    {
        "id": "T0_05",
        "tier": "T0",
        "s4tp_name": "S4TuringPoisson.restrictDom_replaceDom",
        "spec_name": "cal_restrictDom_replaceDom",
        "exclude": ["S4TuringPoisson.restrictDom_replaceDom", "restrictDom_replaceDom"],
        "unsSimp": ["S4TuringPoisson.restrictDom_replaceDom"],
        "statement": (
            "theorem cal_restrictDom_replaceDom {A : Type*} (D : Finset ℤ) (w : D → A) (s : ℤ → A) :\n"
            "    restrictDom D (replaceDom D w s) = w"
        ),
        "gold_proof": "by\n  funext ⟨k, hk⟩\n  simp [restrictDom, replaceDom, hk]",
    },
    {
        "id": "T0_06",
        "tier": "T0",
        "s4tp_name": "S4TuringPoisson.GeneralizedShift.ofTwoDomains_D_self",
        "spec_name": "cal_ofTwoDomains_D_self",
        "exclude": [
            "S4TuringPoisson.GeneralizedShift.ofTwoDomains_D_self",
            "GeneralizedShift.ofTwoDomains_D_self",
            "ofTwoDomains_D_self",
        ],
        "unsSimp": ["S4TuringPoisson.GeneralizedShift.ofTwoDomains_D_self"],
        "statement": (
            "theorem cal_ofTwoDomains_D_self {A : Type*} (D : Finset ℤ) (F : (D → A) → ℤ)\n"
            "    (G : (D → A) → (D → A)) :\n"
            "    (GeneralizedShift.ofTwoDomains D D F G).D = D"
        ),
        "gold_proof": "Finset.union_idempotent (s := D)",
    },
    {
        "id": "T0_07",
        "tier": "T0",
        "s4tp_name": "S4TuringPoisson.mem_shiftDom3_iff",
        "spec_name": "cal_mem_shiftDom3_iff",
        "exclude": ["S4TuringPoisson.mem_shiftDom3_iff", "mem_shiftDom3_iff"],
        "unsSimp": [],
        "statement": "theorem cal_mem_shiftDom3_iff (k : ℤ) : k ∈ shiftDom3 ↔ k = -1 ∨ k = 0 ∨ k = 1",
        "gold_proof": "by\n  simp [shiftDom3]",
    },
    {
        "id": "T0_08",
        "tier": "T0",
        "s4tp_name": "S4TuringPoisson.notMem_shiftDom3_iff",
        "spec_name": "cal_notMem_shiftDom3_iff",
        "exclude": ["S4TuringPoisson.notMem_shiftDom3_iff", "notMem_shiftDom3_iff"],
        "unsSimp": [],
        "statement": "theorem cal_notMem_shiftDom3_iff (k : ℤ) : k ∉ shiftDom3 ↔ k ≠ -1 ∧ k ≠ 0 ∧ k ≠ 1",
        "gold_proof": "by\n  simp [shiftDom3, not_or]",
    },
    {
        "id": "T0_09",
        "tier": "T0",
        "s4tp_name": "S4TuringPoisson.mkDom3_eta",
        "spec_name": "cal_mkDom3_eta",
        "exclude": ["S4TuringPoisson.mkDom3_eta", "mkDom3_eta"],
        "unsSimp": ["S4TuringPoisson.mkDom3_eta"],
        "statement": (
            "theorem cal_mkDom3_eta {A : Type*} (w : shiftDom3 → A) :\n"
            "    mkDom3 (w dom3NegOne) (w dom3Zero) (w dom3One) = w"
        ),
        "gold_proof": "by\n  funext ⟨k, hk⟩\n  rcases (mem_shiftDom3_iff k).mp hk with rfl | rfl | rfl <;> rfl",
    },
    {
        "id": "T0_10",
        "tier": "T0",
        "s4tp_name": "S4TuringPoisson.tape_write_write",
        "spec_name": "cal_tape_write_write",
        "exclude": ["S4TuringPoisson.tape_write_write", "tape_write_write"],
        "unsSimp": ["S4TuringPoisson.tape_write_write"],
        "statement": (
            "theorem cal_tape_write_write {Γ : Type*} [Inhabited Γ] (T : Turing.Tape Γ) (a b : Γ) :\n"
            "    (T.write a).write b = T.write b"
        ),
        "gold_proof": "by\n  cases T\n  rfl",
    },
    {
        "id": "T0_11",
        "tier": "T0",
        "s4tp_name": "S4TuringPoisson.cantorBase_eq_of_two_le",
        "spec_name": "cal_cantorBase_eq_of_two_le",
        "exclude": ["S4TuringPoisson.cantorBase_eq_of_two_le", "cantorBase_eq_of_two_le"],
        "unsSimp": [],
        "statement": "theorem cal_cantorBase_eq_of_two_le {N : ℕ} (hN : 2 ≤ N) : cantorBase N = 2 * N - 1",
        "gold_proof": "by\n  unfold cantorBase\n  omega",
    },
    {
        "id": "T0_12",
        "tier": "T0",
        "s4tp_name": "S4TuringPoisson.three_le_cantorBase",
        "spec_name": "cal_three_le_cantorBase",
        "exclude": ["S4TuringPoisson.three_le_cantorBase", "three_le_cantorBase"],
        "unsSimp": [],
        "statement": "theorem cal_three_le_cantorBase (N : ℕ) : 3 ≤ cantorBase N",
        "gold_proof": "le_max_right _ _",
    },
    {
        "id": "T0_13",
        "tier": "T0",
        "s4tp_name": "S4TuringPoisson.cantorBase_pos",
        "spec_name": "cal_cantorBase_pos",
        "exclude": ["S4TuringPoisson.cantorBase_pos", "cantorBase_pos"],
        "unsSimp": [],
        "statement": "theorem cal_cantorBase_pos (N : ℕ) : 0 < cantorBase N",
        "gold_proof": "lt_of_lt_of_le (by decide : 0 < 3) (three_le_cantorBase N)",
    },
    {
        "id": "T0_14",
        "tier": "T0",
        "s4tp_name": "S4TuringPoisson.cantorCoord_nonneg",
        "spec_name": "cal_cantorCoord_nonneg",
        "exclude": ["S4TuringPoisson.cantorCoord_nonneg", "cantorCoord_nonneg"],
        "unsSimp": [],
        "statement": "theorem cal_cantorCoord_nonneg {N : ℕ} (α : ℕ → Fin N) : 0 ≤ cantorCoord α",
        "gold_proof": "Real.ofDigits_nonneg _",
    },
    {
        "id": "T0_15",
        "tier": "T0",
        "s4tp_name": "S4TuringPoisson.cantorCoord_le_one",
        "spec_name": "cal_cantorCoord_le_one",
        "exclude": ["S4TuringPoisson.cantorCoord_le_one", "cantorCoord_le_one"],
        "unsSimp": [],
        "statement": "theorem cal_cantorCoord_le_one {N : ℕ} (α : ℕ → Fin N) : cantorCoord α ≤ 1",
        "gold_proof": "Real.ofDigits_le_one _",
    },

    # =========================================================================
    # TIER T1 (15 lemmas): structured routine — list induction, ContDiff, TM
    # =========================================================================
    {
        "id": "T1_01",
        "tier": "T1",
        "s4tp_name": "S4TuringPoisson.ReversibleTM.iterate_eval_encodeCfg",
        "spec_name": "cal_iterate_eval_encodeCfg",
        "exclude": [
            "S4TuringPoisson.ReversibleTM.iterate_eval_encodeCfg",
            "ReversibleTM.iterate_eval_encodeCfg",
            "iterate_eval_encodeCfg",
        ],
        "unsSimp": [],
        "statement": (
            "theorem cal_iterate_eval_encodeCfg (R : ReversibleTM) (c : R.Cfg) (n : ℕ) :\n"
            "    R.toGeneralizedShift.eval^[n] (R.encodeCfg c) = R.encodeCfg (R.step^[n] c)"
        ),
        "gold_proof": (
            "by\n  induction n generalizing c with\n"
            "  | zero => rfl\n"
            "  | succ n ih => rw [Function.iterate_succ_apply, R.eval_encodeCfg, ih, Function.iterate_succ_apply]"
        ),
    },
    {
        "id": "T1_02",
        "tier": "T1",
        "s4tp_name": "S4TuringPoisson.FinTM0.iterate_eval_encodeHaltedTape",
        "spec_name": "cal_iterate_eval_encodeHaltedTape",
        "exclude": [
            "S4TuringPoisson.FinTM0.iterate_eval_encodeHaltedTape",
            "FinTM0.iterate_eval_encodeHaltedTape",
            "iterate_eval_encodeHaltedTape",
        ],
        "unsSimp": ["S4TuringPoisson.FinTM0.iterate_eval_encodeHaltedTape"],
        "statement": (
            "theorem cal_iterate_eval_encodeHaltedTape (M : FinTM0) (T : Turing.Tape M.Γ) (n : ℕ) :\n"
            "    M.toGeneralizedShift.eval^[n] (M.encodeHaltedTape T) = M.encodeHaltedTape T"
        ),
        "gold_proof": (
            "by\n  induction n with\n"
            "  | zero => rfl\n"
            "  | succ n ih => rw [Function.iterate_succ_apply', ih, M.eval_encodeHaltedTape]"
        ),
    },
    {
        "id": "T1_03",
        "tier": "T1",
        "s4tp_name": "S4TuringPoisson.FinTM0.encodeActiveCfg_notMem_haltCylinder",
        "spec_name": "cal_encodeActiveCfg_notMem_haltCylinder",
        "exclude": [
            "S4TuringPoisson.FinTM0.encodeActiveCfg_notMem_haltCylinder",
            "FinTM0.encodeActiveCfg_notMem_haltCylinder",
            "encodeActiveCfg_notMem_haltCylinder",
            "S4TuringPoisson.FinTM0.encodeInit_notMem_haltCylinder",
            "encodeInit_notMem_haltCylinder",
        ],
        "unsSimp": [],
        "statement": (
            "theorem cal_encodeActiveCfg_notMem_haltCylinder (M : FinTM0) (c : Turing.TM0.Cfg M.Γ M.Λ)\n"
            "    (k : ℕ) (w : Window M k) :\n"
            "    M.encodeActiveCfg c ∉ cylinderIcc k (M.haltWindow k w)"
        ),
        "gold_proof": (
            "by\n  intro hmem\n"
            "  have h0 : (0 : ℤ) ∈ Set.Icc (-(k : ℤ)) (k : ℤ) := ⟨by omega, by omega⟩\n"
            "  have h := congrArg Prod.snd (hmem ⟨0, h0⟩)\n"
            "  simp [FinTM0.encodeActiveCfg, FinTM0.haltWindow] at h"
        ),
    },
    {
        "id": "T1_04",
        "tier": "T1",
        "s4tp_name": "S4TuringPoisson.FinTM0.encodeHaltedTape_mem_haltCylinder_iff",
        "spec_name": "cal_encodeHaltedTape_mem_haltCylinder_iff",
        "exclude": [
            "S4TuringPoisson.FinTM0.encodeHaltedTape_mem_haltCylinder_iff",
            "FinTM0.encodeHaltedTape_mem_haltCylinder_iff",
            "encodeHaltedTape_mem_haltCylinder_iff",
        ],
        "unsSimp": [],
        "statement": (
            "theorem cal_encodeHaltedTape_mem_haltCylinder_iff (M : FinTM0) (T : Turing.Tape M.Γ) (k : ℕ)\n"
            "    (w : Window M k) :\n"
            "    M.encodeHaltedTape T ∈ cylinderIcc k (M.haltWindow k w) ↔\n"
            "      ∀ i : Set.Icc (-(k : ℤ)) (k : ℤ), T.nth i.1 = w i"
        ),
        "gold_proof": (
            "by\n  constructor\n"
            "  · intro h i\n    exact congrArg Prod.fst (h i)\n"
            "  · intro h i\n    exact Prod.ext (h i) rfl"
        ),
    },
    {
        "id": "T1_05",
        "tier": "T1",
        "s4tp_name": "S4TuringPoisson.continuous_scaledCantorCoord",
        "spec_name": "cal_continuous_scaledCantorCoord",
        "exclude": ["S4TuringPoisson.continuous_scaledCantorCoord", "continuous_scaledCantorCoord"],
        "unsSimp": [],
        "statement": "theorem cal_continuous_scaledCantorCoord {N : ℕ} : Continuous (@scaledCantorCoord N)",
        "gold_proof": "continuous_const.mul continuous_cantorCoord",
    },
    {
        "id": "T1_06",
        "tier": "T1",
        "s4tp_name": "S4TuringPoisson.scaledCantorCoord_mem_Icc",
        "spec_name": "cal_scaledCantorCoord_mem_Icc",
        "exclude": ["S4TuringPoisson.scaledCantorCoord_mem_Icc", "scaledCantorCoord_mem_Icc"],
        "unsSimp": [],
        "statement": (
            "theorem cal_scaledCantorCoord_mem_Icc {N : ℕ} (α : ℕ → Fin N) :\n"
            "    scaledCantorCoord α ∈ Set.Icc (0 : ℝ) (1 / 4)"
        ),
        "gold_proof": (
            "⟨by unfold scaledCantorCoord; linarith [cantorCoord_nonneg α],\n"
            "  by unfold scaledCantorCoord; linarith [cantorCoord_le_one α]⟩"
        ),
    },
    {
        "id": "T1_07",
        "tier": "T1",
        "s4tp_name": "S4TuringPoisson.cantorOpenInterval_nonempty",
        "spec_name": "cal_cantorOpenInterval_nonempty",
        "exclude": ["S4TuringPoisson.cantorOpenInterval_nonempty", "cantorOpenInterval_nonempty"],
        "unsSimp": [],
        "statement": (
            "theorem cal_cantorOpenInterval_nonempty {N m : ℕ} (w : Fin m → Fin N) :\n"
            "    (cantorOpenInterval w).Nonempty"
        ),
        "gold_proof": (
            "by\n  unfold cantorOpenInterval\n"
            "  refine Set.nonempty_Ioo.mpr ?_\n"
            "  have hden : 0 < (4 : ℝ) * (cantorBase N : ℝ) ^ m := by\n"
            "    have := cantorBase_pos N\n    positivity\n"
            "  exact div_lt_div_of_pos_right (by linarith) hden"
        ),
    },
    {
        "id": "T1_08",
        "tier": "T1",
        "s4tp_name": "S4TuringPoisson.continuous_negHalf",
        "spec_name": "cal_continuous_negHalf",
        "exclude": ["S4TuringPoisson.continuous_negHalf", "continuous_negHalf"],
        "unsSimp": [],
        "statement": (
            "theorem cal_continuous_negHalf {A : Type*} [TopologicalSpace A] :\n"
            "    Continuous (@negHalf A)"
        ),
        "gold_proof": "continuous_pi fun j ↦ continuous_apply (-((j : ℤ) + 1))",
    },
    {
        "id": "T1_09",
        "tier": "T1",
        "s4tp_name": "S4TuringPoisson.AreaPreservingDiskIsotopy.contDiff_slice",
        "spec_name": "cal_contDiff_slice",
        "exclude": [
            "S4TuringPoisson.AreaPreservingDiskIsotopy.contDiff_slice",
            "AreaPreservingDiskIsotopy.contDiff_slice",
            "contDiff_slice",
        ],
        "unsSimp": [],
        "statement": (
            "theorem cal_contDiff_slice {r₀ : ℝ} (I : AreaPreservingDiskIsotopy r₀) (t : ℝ) :\n"
            "    ContDiff ℝ ∞ (fun y ↦ I.d (t, y))"
        ),
        "gold_proof": "I.contDiff_d.comp (contDiff_const.prodMk contDiff_id)",
    },
    {
        "id": "T1_10",
        "tier": "T1",
        "s4tp_name": "S4TuringPoisson.AreaPreservingDiskIsotopy.dInv_eq_self_of_notMem_ball",
        "spec_name": "cal_dInv_eq_self_of_notMem_ball",
        "exclude": [
            "S4TuringPoisson.AreaPreservingDiskIsotopy.dInv_eq_self_of_notMem_ball",
            "AreaPreservingDiskIsotopy.dInv_eq_self_of_notMem_ball",
            "dInv_eq_self_of_notMem_ball",
        ],
        "unsSimp": [],
        "statement": (
            "theorem cal_dInv_eq_self_of_notMem_ball {r₀ : ℝ} (I : AreaPreservingDiskIsotopy r₀) (t : ℝ)\n"
            "    {y : EuclideanPlane} (hy : y ∉ Metric.ball (0 : EuclideanPlane) r₀) :\n"
            "    I.dInv (t, y) = y"
        ),
        "gold_proof": (
            "by\n  calc\n"
            "    I.dInv (t, y) = I.dInv (t, I.d (t, y)) := by rw [I.eq_self_of_notMem_ball t y hy]\n"
            "    _ = y := I.left_inv t y"
        ),
    },
    {
        "id": "T1_11",
        "tier": "T1",
        "s4tp_name": "S4TuringPoisson.AreaPreservingDiskIsotopy.dInv_time_zero",
        "spec_name": "cal_dInv_time_zero",
        "exclude": [
            "S4TuringPoisson.AreaPreservingDiskIsotopy.dInv_time_zero",
            "AreaPreservingDiskIsotopy.dInv_time_zero",
            "dInv_time_zero",
        ],
        "unsSimp": ["S4TuringPoisson.AreaPreservingDiskIsotopy.dInv_time_zero"],
        "statement": (
            "theorem cal_dInv_time_zero {r₀ : ℝ} (I : AreaPreservingDiskIsotopy r₀) (y : EuclideanPlane) :\n"
            "    I.dInv (0, y) = y"
        ),
        "gold_proof": (
            "by\n  calc\n"
            "    I.dInv (0, y) = I.dInv (0, I.d (0, y)) := by rw [I.time_zero y]\n"
            "    _ = y := I.left_inv 0 y"
        ),
    },
    {
        "id": "T1_12",
        "tier": "T1",
        "s4tp_name": "S4TuringPoisson.AreaPreservingDiskIsotopy.listComp_diskTimeOneMap",
        "spec_name": "cal_listComp_diskTimeOneMap",
        "exclude": [
            "S4TuringPoisson.AreaPreservingDiskIsotopy.listComp_diskTimeOneMap",
            "AreaPreservingDiskIsotopy.listComp_diskTimeOneMap",
            "listComp_diskTimeOneMap",
        ],
        "unsSimp": ["S4TuringPoisson.AreaPreservingDiskIsotopy.listComp_diskTimeOneMap"],
        "statement": (
            "theorem cal_listComp_diskTimeOneMap {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)\n"
            "    (Is : List (AreaPreservingDiskIsotopy r₀)) :\n"
            "    (AreaPreservingDiskIsotopy.listComp hr₀ Is).diskTimeOneMap =\n"
            "      Is.foldr (fun I acc ↦ I.diskTimeOneMap ∘ acc) id"
        ),
        "gold_proof": (
            "by\n  induction Is with\n"
            "  | nil => exact AreaPreservingDiskIsotopy.refl_diskTimeOneMap hr₀\n"
            "  | cons I Is ih =>\n"
            "    rw [AreaPreservingDiskIsotopy.listComp_cons, AreaPreservingDiskIsotopy.compSame_diskTimeOneMap, ih]\n"
            "    rfl"
        ),
    },
    {
        "id": "T1_13",
        "tier": "T1",
        "s4tp_name": "S4TuringPoisson.listToDiskIsotopy_append_diskTimeOneMap",
        "spec_name": "cal_listToDiskIsotopy_append_diskTimeOneMap",
        "exclude": [
            "S4TuringPoisson.listToDiskIsotopy_append_diskTimeOneMap",
            "listToDiskIsotopy_append_diskTimeOneMap",
        ],
        "unsSimp": [],
        "statement": (
            "theorem cal_listToDiskIsotopy_append_diskTimeOneMap {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)\n"
            "    (Ps₂ Ps₁ : List (CompactlySupportedPlanarHamiltonian r₀)) :\n"
            "    (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy hr₀ (Ps₂ ++ Ps₁)).diskTimeOneMap =\n"
            "      (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy hr₀ Ps₂).diskTimeOneMap ∘\n"
            "        (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy hr₀ Ps₁).diskTimeOneMap"
        ),
        "gold_proof": (
            "by\n  induction Ps₂ with\n"
            "  | nil =>\n"
            "    simp only [List.nil_append, CompactlySupportedPlanarHamiltonian.listToDiskIsotopy_nil,\n"
            "      AreaPreservingDiskIsotopy.refl_diskTimeOneMap, Function.id_comp]\n"
            "  | cons P Ps₂ ih =>\n"
            "    simp only [List.cons_append, CompactlySupportedPlanarHamiltonian.listToDiskIsotopy_cons,\n"
            "      AreaPreservingDiskIsotopy.compSame_diskTimeOneMap, ih, Function.comp_assoc]"
        ),
    },
    {
        "id": "T1_14",
        "tier": "T1",
        "s4tp_name": "S4TuringPoisson.RealizesGeneralizedShiftByHamiltonians.append",
        "spec_name": "cal_RealizesGeneralizedShiftByHamiltonians_append",
        "exclude": [
            "S4TuringPoisson.RealizesGeneralizedShiftByHamiltonians.append",
            "RealizesGeneralizedShiftByHamiltonians.append",
        ],
        "unsSimp": [],
        "statement": (
            "theorem cal_RealizesGeneralizedShiftByHamiltonians_append {A : Type*} {N : ℕ} (enc : A ≃ Fin N)\n"
            "    {Φ₂ Φ₁ : GeneralizedShift A} {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1)\n"
            "    {Ps₂ Ps₁ : List (CompactlySupportedPlanarHamiltonian r₀)}\n"
            "    (h₂ : RealizesGeneralizedShiftByHamiltonians enc Φ₂ hr₀ Ps₂)\n"
            "    (h₁ : RealizesGeneralizedShiftByHamiltonians enc Φ₁ hr₀ Ps₁) :\n"
            "    ∀ s : ℤ → A,\n"
            "      (CompactlySupportedPlanarHamiltonian.listToDiskIsotopy hr₀ (Ps₂ ++ Ps₁)).diskTimeOneMap\n"
            "          (cantorDiskEmbed enc s) =\n"
            "        cantorDiskEmbed enc (Φ₂.eval (Φ₁.eval s))"
        ),
        "gold_proof": (
            "by\n  intro s\n"
            "  rw [listToDiskIsotopy_append_diskTimeOneMap, Function.comp_apply, h₁ s, h₂ (Φ₁.eval s)]"
        ),
    },
    {
        "id": "T1_15",
        "tier": "T1",
        "s4tp_name": "S4TuringPoisson.contDiff_rotQuad",
        "spec_name": "cal_contDiff_rotQuad",
        "exclude": ["S4TuringPoisson.contDiff_rotQuad", "contDiff_rotQuad"],
        "unsSimp": [],
        "statement": "theorem cal_contDiff_rotQuad (c : EuclideanPlane) (θ : ℝ) : ContDiff ℝ ∞ (rotQuad c θ)",
        "gold_proof": (
            "by\n  unfold rotQuad\n"
            "  have hy0 : ContDiff ℝ ∞ (fun y : EuclideanPlane ↦ y 0) := (planeCoordCLM 0).contDiff\n"
            "  have hy1 : ContDiff ℝ ∞ (fun y : EuclideanPlane ↦ y 1) := (planeCoordCLM 1).contDiff\n"
            "  exact contDiff_const.mul\n"
            "    (((hy0.sub contDiff_const).pow 2).add ((hy1.sub contDiff_const).pow 2))"
        ),
    },

    # =========================================================================
    # TIER T2 (10 lemmas): core analysis / geometry / Cantor / Primrec
    # =========================================================================
    {
        "id": "T2_01",
        "tier": "T2",
        "s4tp_name": "S4TuringPoisson.GeneralizedShift.eval_ofTwoDomains",
        "spec_name": "cal_eval_ofTwoDomains",
        "exclude": [
            "S4TuringPoisson.GeneralizedShift.eval_ofTwoDomains",
            "GeneralizedShift.eval_ofTwoDomains",
            "eval_ofTwoDomains",
        ],
        "unsSimp": [],
        "statement": (
            "theorem cal_eval_ofTwoDomains {A : Type*} (D_F D_G : Finset ℤ) (F : (D_F → A) → ℤ)\n"
            "    (G : (D_G → A) → (D_G → A)) (s : ℤ → A) :\n"
            "    (GeneralizedShift.ofTwoDomains D_F D_G F G).eval s =\n"
            "      shiftSeq (F (restrictDom D_F s)) (replaceDom D_G (G (restrictDom D_G s)) s)"
        ),
        "gold_proof": (
            "by\n  funext k\n"
            "  unfold GeneralizedShift.eval GeneralizedShift.ofTwoDomains shiftSeq restrictDom replaceDom\n"
            "  dsimp only\n"
            "  by_cases hG : (k + F fun i ↦ s i.1) ∈ D_G\n"
            "  · have hU : (k + F fun i ↦ s i.1) ∈ D_F ∪ D_G := Finset.mem_union_right D_F hG\n"
            "    simp [hU, hG]\n"
            "  · by_cases hU : (k + F fun i ↦ s i.1) ∈ D_F ∪ D_G <;> simp [hU, hG]"
        ),
    },
    {
        "id": "T2_02",
        "tier": "T2",
        "s4tp_name": "S4TuringPoisson.ReversibleTM.invStep_step",
        "spec_name": "cal_invStep_step",
        "exclude": [
            "S4TuringPoisson.ReversibleTM.invStep_step",
            "ReversibleTM.invStep_step",
            "invStep_step",
        ],
        "unsSimp": ["S4TuringPoisson.ReversibleTM.invStep_step"],
        "statement": "theorem cal_invStep_step (R : ReversibleTM) (c : R.Cfg) : R.invStep (R.step c) = c",
        "gold_proof": (
            "by\n  rcases c with ⟨q, ⟨hd, L, Rt⟩⟩\n"
            "  dsimp only [ReversibleTM.step, ReversibleTM.invStep]\n"
            "  generalize hqb : R.stepPerm (q, hd) = qb\n"
            "  rcases qb with ⟨q', b⟩\n"
            "  have hsymm : R.stepPerm.symm (q', b) = (q, hd) := R.stepPerm.symm_apply_eq.mpr hqb.symm\n"
            "  rcases hdir : R.dirIn q' <;> simp [hdir, Turing.Tape.write, hsymm]"
        ),
    },
    {
        "id": "T2_03",
        "tier": "T2",
        "s4tp_name": "S4TuringPoisson.cantorPrefixCode_add_one_le_pow",
        "spec_name": "cal_cantorPrefixCode_add_one_le_pow",
        "exclude": [
            "S4TuringPoisson.cantorPrefixCode_add_one_le_pow",
            "cantorPrefixCode_add_one_le_pow",
            "S4TuringPoisson.cantorPrefixCode_le_pow_sub_one",
            "cantorPrefixCode_le_pow_sub_one",
        ],
        "unsSimp": [],
        "statement": (
            "theorem cal_cantorPrefixCode_add_one_le_pow (B : ℕ) (hB : 1 ≤ B) {m : ℕ}\n"
            "    (w : Fin m → ℕ) (hw : ∀ j : Fin m, 2 * w j ≤ B - 1) :\n"
            "    cantorPrefixCode B w + 1 ≤ B ^ m"
        ),
        "gold_proof": (
            "by\n  induction m with\n"
            "  | zero => simp [cantorPrefixCode]\n"
            "  | succ m ih =>\n"
            "    have ih' := ih (fun j : Fin m ↦ w j.castSucc) (fun j ↦ hw j.castSucc)\n"
            "    have hlast : 2 * w (Fin.last m) + 1 ≤ B := by have := hw (Fin.last m); omega\n"
            "    calc\n"
            "      cantorPrefixCode B w + 1\n"
            "          = B * cantorPrefixCode B (fun j : Fin m ↦ w j.castSucc) + (2 * w (Fin.last m) + 1) := by\n"
            "            simp [cantorPrefixCode, add_assoc]\n"
            "      _ ≤ B * cantorPrefixCode B (fun j : Fin m ↦ w j.castSucc) + B := Nat.add_le_add_left hlast _\n"
            "      _ = B * (cantorPrefixCode B (fun j : Fin m ↦ w j.castSucc) + 1) := by ring\n"
            "      _ ≤ B * B ^ m := Nat.mul_le_mul_left B ih'\n"
            "      _ = B ^ (m + 1) := (pow_succ' B m).symm"
        ),
    },
    {
        "id": "T2_04",
        "tier": "T2",
        "s4tp_name": "S4TuringPoisson.sum_ofDigitsTerm_cantorEvenDigit",
        "spec_name": "cal_sum_ofDigitsTerm_cantorEvenDigit",
        "exclude": [
            "S4TuringPoisson.sum_ofDigitsTerm_cantorEvenDigit",
            "sum_ofDigitsTerm_cantorEvenDigit",
            "S4TuringPoisson.cantorCoord_eq_prefix_add_tail",
            "cantorCoord_eq_prefix_add_tail",
        ],
        "unsSimp": [],
        "statement": (
            "theorem cal_sum_ofDigitsTerm_cantorEvenDigit {N : ℕ} (α : ℕ → Fin N) (m : ℕ) :\n"
            "    (∑ i ∈ Finset.range m, Real.ofDigitsTerm (fun j ↦ cantorEvenDigit (α j)) i) =\n"
            "      (cantorPrefixCode (cantorBase N) (fun j : Fin m ↦ (α j.1).1) : ℝ) /\n"
            "        ((cantorBase N : ℝ) ^ m)"
        ),
        "gold_proof": (
            "by\n  have hB0 : (cantorBase N : ℝ) ≠ 0 := by exact_mod_cast (cantorBase_pos N).ne'\n"
            "  induction m with\n"
            "  | zero => simp [cantorPrefixCode]\n"
            "  | succ m ih =>\n"
            "    rw [Finset.sum_range_succ, ih]\n"
            "    simp only [Real.ofDigitsTerm, cantorEvenDigit, cantorPrefixCode, Fin.val_last,\n"
            "      Fin.val_castSucc, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, pow_succ]\n"
            "    field_simp [hB0]"
        ),
    },
    {
        "id": "T2_05",
        "tier": "T2",
        "s4tp_name": "S4TuringPoisson.scaledCantorCoord_injective",
        "spec_name": "cal_scaledCantorCoord_injective",
        "exclude": [
            "S4TuringPoisson.scaledCantorCoord_injective",
            "scaledCantorCoord_injective",
            "S4TuringPoisson.cantorDiskEmbed_injective",
            "cantorDiskEmbed_injective",
        ],
        "unsSimp": [],
        "statement": "theorem cal_scaledCantorCoord_injective {N : ℕ} : Function.Injective (@scaledCantorCoord N)",
        "gold_proof": (
            "by\n  intro α β h\n  funext i\n"
            "  let w : Fin (i + 1) → Fin N := fun j ↦ α j.1\n"
            "  have hα : scaledCantorCoord α ∈ cantorOpenInterval w :=\n"
            "    (scaledCantorCoord_mem_cantorOpenInterval_iff α w).mpr fun _ ↦ rfl\n"
            "  rw [h] at hα\n"
            "  have hβ := (scaledCantorCoord_mem_cantorOpenInterval_iff β w).mp hα (Fin.last i)\n"
            "  simpa [w] using hβ.symm"
        ),
    },
    {
        "id": "T2_06",
        "tier": "T2",
        "s4tp_name": "S4TuringPoisson.cantorPrefixPairList_snd",
        "spec_name": "cal_cantorPrefixPairList_snd",
        "exclude": ["S4TuringPoisson.cantorPrefixPairList_snd", "cantorPrefixPairList_snd"],
        "unsSimp": [],
        "statement": (
            "theorem cal_cantorPrefixPairList_snd (B : ℕ) (digits : List ℕ) :\n"
            "    (cantorPrefixPairList B digits).2 = B ^ digits.length"
        ),
        "gold_proof": (
            "by\n  unfold cantorPrefixPairList\n"
            "  have hgen : ∀ (l : List ℕ) (a p : ℕ),\n"
            "      (l.foldl (fun acc d ↦ (B * acc.1 + 2 * d, B * acc.2)) (a, p)).2 = p * B ^ l.length := by\n"
            "    intro l\n    induction l with\n    | nil => simp\n    | cons d l ih =>\n"
            "      intro a p\n      simp only [List.foldl_cons, List.length_cons, ih, pow_succ]\n      ring\n"
            "  simpa using hgen digits 0 1"
        ),
    },
    {
        "id": "T2_07",
        "tier": "T2",
        "s4tp_name": "S4TuringPoisson.primrec_approxCantorList",
        "spec_name": "cal_primrec_approxCantorList",
        "exclude": ["S4TuringPoisson.primrec_approxCantorList", "primrec_approxCantorList"],
        "unsSimp": [],
        "statement": "theorem cal_primrec_approxCantorList (B : ℕ) : Primrec (approxCantorList B)",
        "gold_proof": (
            "by\n  unfold approxCantorList mkPosQuarterRatFrac\n"
            "  have hp := primrec_cantorPrefixPairList B\n"
            "  exact Primrec.pair (Primrec.const false)\n"
            "    (Primrec.pair (Primrec.fst.comp hp)\n"
            "      (Primrec.nat_sub.comp\n"
            "        (Primrec.nat_mul.comp (Primrec.const 4) (Primrec.snd.comp hp))\n"
            "        (Primrec.const 1)))"
        ),
    },
    {
        "id": "T2_08",
        "tier": "T2",
        "s4tp_name": "S4TuringPoisson.norm_planeRotate",
        "spec_name": "cal_norm_planeRotate",
        "exclude": ["S4TuringPoisson.norm_planeRotate", "norm_planeRotate"],
        "unsSimp": ["S4TuringPoisson.norm_planeRotate"],
        "statement": "theorem cal_norm_planeRotate (α : ℝ) (v : EuclideanPlane) : ‖planeRotate α v‖ = ‖v‖",
        "gold_proof": (
            "by\n  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_two, Fin.sum_univ_two]\n"
            "  simp only [planeRotate, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,\n"
            "    Real.norm_eq_abs, sq_abs]\n"
            "  congr 1\n"
            "  calc\n"
            "    (Real.cos α * v 0 - Real.sin α * v 1) ^ 2 + (Real.sin α * v 0 + Real.cos α * v 1) ^ 2\n"
            "        = (Real.cos α ^ 2 + Real.sin α ^ 2) * (v 0 ^ 2 + v 1 ^ 2) := by ring\n"
            "    _ = 1 * (v 0 ^ 2 + v 1 ^ 2) := by rw [Real.cos_sq_add_sin_sq]\n"
            "    _ = v 0 ^ 2 + v 1 ^ 2 := one_mul _"
        ),
    },
    {
        "id": "T2_09",
        "tier": "T2",
        "s4tp_name": "S4TuringPoisson.disjoint_symmetric_closedBalls",
        "spec_name": "cal_disjoint_symmetric_closedBalls",
        "exclude": ["S4TuringPoisson.disjoint_symmetric_closedBalls", "disjoint_symmetric_closedBalls"],
        "unsSimp": [],
        "statement": (
            "theorem cal_disjoint_symmetric_closedBalls {a : EuclideanPlane} {ρ : ℝ} (hρ : ρ < ‖a‖) :\n"
            "    Disjoint (Metric.closedBall (-a) ρ) (Metric.closedBall a ρ)"
        ),
        "gold_proof": (
            "by\n  rw [Set.disjoint_iff]\n"
            "  rintro y ⟨h1, h2⟩\n"
            "  have hd1 : dist y (-a) ≤ ρ := Metric.mem_closedBall.mp h1\n"
            "  have hd2 : dist a y ≤ ρ := by rw [dist_comm]; exact Metric.mem_closedBall.mp h2\n"
            "  have h2a : dist a (-a) = 2 * ‖a‖ := by\n"
            "    rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ a, norm_smul, Real.norm_of_nonneg (by norm_num)]\n"
            "  have htri : dist a (-a) ≤ dist a y + dist y (-a) := dist_triangle a y (-a)\n"
            "  linarith"
        ),
    },
    {
        "id": "T2_10",
        "tier": "T2",
        "s4tp_name": "S4TuringPoisson.bumpedHyperbolicStretchIsotopy_cantorBase_timeOne",
        "spec_name": "cal_bumpedHyperbolicStretchIsotopy_cantorBase_timeOne",
        "exclude": [
            "S4TuringPoisson.bumpedHyperbolicStretchIsotopy_cantorBase_timeOne",
            "bumpedHyperbolicStretchIsotopy_cantorBase_timeOne",
        ],
        "unsSimp": [],
        "statement": (
            "theorem cal_bumpedHyperbolicStretchIsotopy_cantorBase_timeOne {r₀ : ℝ}\n"
            "    (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) 1) (c : EuclideanPlane) {r_out δ : ℝ} (hr_out : 0 < r_out)\n"
            "    (hsub : Metric.ball c r_out ⊆ Metric.ball (0 : EuclideanPlane) r₀) (N : ℕ)\n"
            "    (hδ : Real.exp (2 * |Real.log (cantorBase N : ℝ)|) * δ < r_out / 2)\n"
            "    {y₀ : EuclideanPlane} (hy₀ : y₀ ∈ Metric.closedBall c δ) :\n"
            "    (bumpedHyperbolicStretchIsotopy hr₀ c hr_out hsub (Real.log (cantorBase N : ℝ))).d (1, y₀) =\n"
            "      c + WithLp.toLp 2\n"
            "        ![(cantorBase N : ℝ)⁻¹ * (y₀ 0 - c 0), (cantorBase N : ℝ) * (y₀ 1 - c 1)]"
        ),
        "gold_proof": (
            "by\n  have hB : 0 < (cantorBase N : ℝ) := by exact_mod_cast cantorBase_pos N\n"
            "  rw [bumpedHyperbolicStretchIsotopy_timeOne_of_mem_closedBall hr₀ c hr_out hsub\n"
            "    (Real.log (cantorBase N : ℝ)) hδ hy₀, Real.exp_neg, Real.exp_log hB]"
        ),
    },
]


def render_item_spec(item: Dict[str, Any], use_gold: bool = False) -> str:
    """Render a standalone spec file for a single benchmark item."""
    lines = [COMMON_PREAMBLE.strip(), ""]
    for u in item.get("unsSimp", []):
        lines.append(f"attribute [-simp] {u}")
    lines.append(f"-- Original S4TuringPoisson lemma: {item['s4tp_name']}")
    lines.append(f"-- tier: {item['tier']}")
    body = item["gold_proof"] if use_gold else "by\n  sorry"
    lines.append(f"{item['statement']} :=\n  {body}\n")
    return "\n".join(lines)


def verify_all_gold_proofs(repo_root: Path) -> int:
    """Verify in a single Lean check that all 40 gold benchmark declarations compile cleanly."""
    lines = [COMMON_PREAMBLE.strip(), ""]
    for item in CALIBRATION_BENCHMARK:
        for u in item.get("unsSimp", []):
            lines.append(f"attribute [-simp] {u}")
        lines.append(f"-- {item['id']} ({item['tier']}): {item['s4tp_name']}")
        lines.append(f"{item['statement']} :=\n  {item['gold_proof']}\n")

    with tempfile.TemporaryDirectory() as td:
        gold_file = Path(td) / "GoldVerify.lean"
        gold_file.write_text("\n".join(lines), encoding="utf-8")
        accepted, rc, diag, lean_ms, _ = gemma_loop.run_lean_check(gold_file, repo_root, timeout_sec=180.0)
        if not accepted:
            print(f"[FAIL] Gold verification failed (rc={rc}, {lean_ms:.0f}ms):\n{diag}", file=sys.stderr)
            return 1
        print(f"[OK] All {len(CALIBRATION_BENCHMARK)} gold proofs verified cleanly in {lean_ms:.0f} ms!")
        return 0


def run_benchmark(
    repo_root: Path,
    max_attempts: int = 5,
    milestone: str = "GM1",
    filter_tier: Optional[str] = None,
    filter_id: Optional[str] = None,
    limit: Optional[int] = None,
    resume: bool = False,
    output_json: Optional[Path] = None,
) -> Dict[str, Any]:
    """Run the compiler-in-the-loop calibration benchmark on the 40 stratified S4TuringPoisson lemmas."""
    idx = bm25_index.RepositoryIndex.load_or_build(repo_root=repo_root)
    specs_dir = repo_root / ".agents" / "gemma_scratch" / "calibration_specs"
    specs_dir.mkdir(parents=True, exist_ok=True)

    results: List[Dict[str, Any]] = []
    prior_wall = 0.0
    completed_ids = set()
    if resume and output_json and output_json.is_file():
        try:
            prev_data = json.loads(output_json.read_text(encoding="utf-8"))
            results = prev_data.get("results", [])
            prior_wall = float(prev_data.get("total_wall_seconds") or sum(r.get("wall_seconds", 0.0) for r in results))
            completed_ids = {r["id"] for r in results if r.get("id")}
        except Exception:
            results = []

    items = [
        it for it in CALIBRATION_BENCHMARK
        if (not filter_tier or it["tier"] == filter_tier)
        and (not filter_id or it["id"] == filter_id)
        and (it["id"] not in completed_ids)
    ]
    if limit is not None and limit > 0:
        items = items[:limit]

    t_start = time.time()

    for _idx_num, item in enumerate(items, 1):
        if workflow_control.WorkflowController(repo_root).is_paused():
            print("[PAUSED] Stopping calibration benchmark.", file=sys.stderr)
            break

        spec_path = specs_dir / f"{item['id']}_{item['spec_name']}.lean"
        spec_path.write_text(render_item_spec(item, use_gold=False), encoding="utf-8")

        item_t0 = time.time()
        res = gemma_loop.prove_spec_file(
            spec_path=spec_path,
            repo_root=repo_root,
            tier_override=item["tier"],
            max_attempts=max_attempts,
            milestone=milestone,
            exclude=item["exclude"],
            idx=idx,
        )
        wall_s = time.time() - item_t0
        decl_res = res["results"][0] if res.get("results") else {}
        accepted = bool(decl_res.get("accepted"))
        acc_attempt = decl_res.get("accepted_at_attempt")
        attempts = decl_res.get("attempts", [])
        total_tok = sum(int(a.get("tokens", 0)) for a in attempts)

        rec = {
            "id": item["id"],
            "tier": item["tier"],
            "s4tp_name": item["s4tp_name"],
            "spec_name": item["spec_name"],
            "accepted": accepted,
            "accepted_at_attempt": acc_attempt,
            "attempts_used": len(attempts),
            "wall_seconds": round(wall_s, 2),
            "total_tokens": total_tok,
            "attempts": attempts,
        }
        results.append(rec)
        status_str = f"PASS@{acc_attempt}" if accepted else f"FAIL({len(attempts)})"
        print(
            f"[{len(results):02d}/40] {item['id']} ({item['tier']}) "
            f"{item['s4tp_name']:<55} -> {status_str:<8} ({wall_s:.1f}s, {total_tok} tok)",
            flush=True,
        )

        if output_json:
            output_json.parent.mkdir(parents=True, exist_ok=True)
            cur_wall = prior_wall + (time.time() - t_start)
            output_json.write_text(
                json.dumps({"total_wall_seconds": round(cur_wall, 2), "results": results}, indent=2) + "\n",
                encoding="utf-8",
            )

    total_wall = prior_wall + (time.time() - t_start)
    payload = {"total_wall_seconds": round(total_wall, 2), "results": results}
    if output_json:
        output_json.parent.mkdir(parents=True, exist_ok=True)
        output_json.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return payload


def main() -> int:
    parser = argparse.ArgumentParser(description="Run GM1 40-lemma stratified gemma4:12B calibration benchmark")
    parser.add_argument("--root", default=None, help="Override repository root")
    parser.add_argument("--verify-gold", action="store_true", help="Verify all 40 gold S4TuringPoisson proofs compile")
    parser.add_argument("--max-attempts", type=int, default=5, help="Max attempts per lemma (default 5)")
    parser.add_argument("--milestone", default="GM1", help="Ledger milestone label (default GM1)")
    parser.add_argument("--tier", choices=["T0", "T1", "T2"], default=None, help="Filter by tier")
    parser.add_argument("--id", default=None, help="Filter by single benchmark item ID (e.g. T0_01)")
    parser.add_argument("--limit", type=int, default=None, help="Run at most N items in this invocation")
    parser.add_argument("--resume", action="store_true", help="Resume from existing output JSON")
    parser.add_argument(
        "--output",
        default=".agents/gemma_scratch/calibration_results.json",
        help="Path to save incremental calibration JSON results",
    )
    args = parser.parse_args()

    root = bm25_index.resolve_repo_root(args.root)
    if args.verify_gold:
        return verify_all_gold_proofs(root)

    out_path = Path(args.output)
    if not out_path.is_absolute():
        out_path = root / out_path
    run_benchmark(
        repo_root=root,
        max_attempts=args.max_attempts,
        milestone=args.milestone,
        filter_tier=args.tier,
        filter_id=args.id,
        limit=args.limit,
        resume=args.resume,
        output_json=out_path,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
