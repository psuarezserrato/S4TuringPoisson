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

public import S4TuringPoisson.Fibration.S4Fibration
public import S4TuringPoisson.Fibration.WrinkledGeneral4Manifold

/-!
# Purely Wrinkled Fibrations (`L-R1`) and Definite-Fold Exclusion Witness

This file implements Deliverable `L-R1` of `MISSION_DIRECTIVE_LEKILI.md` and the Gate G5.1
anti-vacuity definite-fold exclusion proof on `s4Fibration`:

1. **`PurelyWrinkledFibration` (`Lekili 2009`, `Suárez-Serrato–Torres 2016`)**:
   - Extends `WrinkledFibration I_M M I_B Base Fiber` with the constraint that every critical
     point `p ∈ criticalPoints I_M I_B toFun` is locally modeled either on an indefinite
     quadratic fold (`IsIndefiniteFoldAt`) or on a wrinkled cusp (`IsWrinkledCuspAt`).
   - Provides `BrokenLefschetzFibration.toPurelyWrinkledOfIndefiniteFolds` converting any
     lefschetz-free broken Lefschetz fibration into a `PurelyWrinkledFibration`.
   - Provides `AdmitsWrinkledOrBrokenLefschetzFibration.ofPurelyWrinkled`, mirroring
     `AdmitsWrinkledOrBrokenLefschetzFibration.ofBrokenLefschetz`.

2. **Gate G5.1 Definite-Fold Exclusion Witness (`not_isIndefiniteFoldAt_s4Fibration`,
   `not_isWrinkledCuspAt_s4Fibration`, `not_isRealLefschetzAt_s4Fibration`)**:
   - Proves that each of the three non-definite model maps `indefiniteFoldMap`,
     `wrinkledCuspMap`, and `realLefschetzMap` maps every open ball around `0 : ℝ⁴` onto a
     neighborhood of `0 : ℝ²`, so any map locally modeled on one of them at `p` contains an open
     neighborhood of `f p` in `Set.range f`.
   - Proves that the explicit definite-fold fibration `s4Fibration : Sphere4 → Sphere2` satisfies
     `‖s4ProjPlane p.1‖ = 1` at critical points and `‖s4ProjPlane q.1‖ ≤ 1` globally, so
     `Set.range s4Fibration` contains no neighborhood of `s4Fibration p` for any critical point
     `p`. Hence `s4Fibration` admits neither a `BrokenLefschetzFibration` nor a
     `PurelyWrinkledFibration` lift, confirming non-vacuity of those stronger classes.
-/

@[expose] public section

open Function Metric Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace S4TuringPoisson

/-! ## 1. `PurelyWrinkledFibration` Structure and Typeclass Bridge (`L-R1`) -/

section PurelyWrinkledStructure

universe u v w

/-- A **purely wrinkled fibration** (`Lekili 2009`, `ST16`) is a `WrinkledFibration` every one of
whose critical points is locally modeled either on an indefinite quadratic fold
(`IsIndefiniteFoldAt`) or on a wrinkled cusp singularity (`IsWrinkledCuspAt`), with zero real
Lefschetz points and zero definite folds. -/
structure PurelyWrinkledFibration
    {E_M H_M : Type*} [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    (I_M : ModelWithCorners ℝ E_M H_M) (M : Type u)
    [TopologicalSpace M] [ChartedSpace H_M M] [IsManifold I_M ∞ M]
    {E_B H_B : Type*} [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    (I_B : ModelWithCorners ℝ E_B H_B) (Base : Type v)
    [TopologicalSpace Base] [ChartedSpace H_B Base] [IsManifold I_B ∞ Base]
    (Fiber : Type w) [TopologicalSpace Fiber] [ChartedSpace EuclideanPlane Fiber]
    [IsManifold (𝓡 2) ∞ Fiber] [T2Space Fiber] [CompactSpace Fiber] [Nonempty Fiber] :
    Type (max u v w)
    extends WrinkledFibration I_M M I_B Base Fiber where
  /-- Every critical point is an indefinite quadratic fold or a wrinkled cusp. -/
  singularities_purely_wrinkled :
    ∀ p ∈ criticalPoints I_M I_B toFun,
      IsIndefiniteFoldAt I_M I_B toFun p ∨ IsWrinkledCuspAt I_M I_B toFun p

instance instCoeFunPurelyWrinkledFibration
    {E_M H_M : Type*} [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    {I_M : ModelWithCorners ℝ E_M H_M} {M : Type u}
    [TopologicalSpace M] [ChartedSpace H_M M] [IsManifold I_M ∞ M]
    {E_B H_B : Type*} [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    {I_B : ModelWithCorners ℝ E_B H_B} {Base : Type v}
    [TopologicalSpace Base] [ChartedSpace H_B Base] [IsManifold I_B ∞ Base]
    {Fiber : Type w} [TopologicalSpace Fiber] [ChartedSpace EuclideanPlane Fiber]
    [IsManifold (𝓡 2) ∞ Fiber] [T2Space Fiber] [CompactSpace Fiber] [Nonempty Fiber] :
    CoeFun (PurelyWrinkledFibration I_M M I_B Base Fiber) (fun _ ↦ M → Base) :=
  ⟨fun P ↦ P.toFun⟩

/-- Convert a `BrokenLefschetzFibration` having no real Lefschetz critical points (only
indefinite folds) directly into a `PurelyWrinkledFibration`. -/
noncomputable def BrokenLefschetzFibration.toPurelyWrinkledOfIndefiniteFolds
    {E_M H_M : Type*} [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    {I_M : ModelWithCorners ℝ E_M H_M} {M : Type u}
    [TopologicalSpace M] [ChartedSpace H_M M] [IsManifold I_M ∞ M]
    {E_B H_B : Type*} [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    {I_B : ModelWithCorners ℝ E_B H_B} {Base : Type v}
    [TopologicalSpace Base] [ChartedSpace H_B Base] [IsManifold I_B ∞ Base]
    {F : Type w} [TopologicalSpace F] [ChartedSpace EuclideanPlane F]
    [IsManifold (𝓡 2) ∞ F] [T2Space F] [CompactSpace F] [Nonempty F]
    (B_fib : BrokenLefschetzFibration I_M M I_B Base F)
    (hfold : ∀ p ∈ criticalPoints I_M I_B B_fib.toFun,
      IsIndefiniteFoldAt I_M I_B B_fib.toFun p) :
    PurelyWrinkledFibration I_M M I_B Base F where
  toWrinkledFibration := B_fib.toWrinkledFibration
  singularities_purely_wrinkled p hp := Or.inl (hfold p hp)

/-- Construct `AdmitsWrinkledOrBrokenLefschetzFibration M` from a positively co-oriented
`PurelyWrinkledFibration` (`Lekili 2009`). -/
-- tier: T2
@[instance_reducible]
noncomputable def AdmitsWrinkledOrBrokenLefschetzFibration.ofPurelyWrinkled
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    (V_M : PositiveVolumeForm (𝓡 4) M)
    (F : Type) [TopologicalSpace F] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) F]
    [IsManifold (𝓡 2) ∞ F] [T2Space F] [CompactSpace F] [Nonempty F]
    [MeasurableSpace F] [BorelSpace F]
    (P_fib : PurelyWrinkledFibration (𝓡 4) M (𝓡 2) Sphere2 F)
    (V_F : PositiveVolumeForm (𝓡 2) F)
    (hpos : ∀ u : P_fib.toWrinkledFibration.preimageOpen, ∃ c : ℝ, 0 < c ∧
      (TauCeti.SmoothForm.mpullback P_fib.trivialization P_fib.trivialization.contMDiff
          (TauCeti.SmoothForm.wedge
            (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd V_F.Ω)
            (TauCeti.SmoothForm.mpullback (Subtype.val ∘ Prod.fst)
              (contMDiff_subtype_val.comp contMDiff_fst) S2VolumeForm))).1 u =
        c • (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val V_M.Ω).1 u) :
    AdmitsWrinkledOrBrokenLefschetzFibration M where
  ambientVolume := V_M
  Fiber := F
  instTopologicalSpaceFiber := inferInstance
  instChartedSpaceFiber := inferInstance
  instIsManifoldFiber := inferInstance
  instT2SpaceFiber := inferInstance
  instCompactSpaceFiber := inferInstance
  instNonemptyFiber := inferInstance
  instMeasurableSpaceFiber := inferInstance
  instBorelSpaceFiber := inferInstance
  fibration := P_fib.toWrinkledFibration
  fiberVolume := V_F
  trivialization_pos_cooriented := hpos

end PurelyWrinkledStructure

/-! ## 2. Local Openness of Non-Definite Singularity Models and Definite-Fold Exclusion -/

section DefiniteFoldExclusion

/-- Norm-squared expansion on `EuclideanSpace ℝ (Fin 4)`. -/
theorem norm_sq_vec4 (p : EuclideanSpace ℝ (Fin 4)) :
    ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_four]
  simp [Real.norm_eq_abs, sq_abs]

private theorem norm_lt_of_sq_lt_sq {E : Type*} [NormedAddCommGroup E] {x : E} {r : ℝ}
    (hr : 0 ≤ r) (hsq : ‖x‖ ^ 2 < r ^ 2) : ‖x‖ < r :=
  lt_of_not_ge fun hle ↦ not_lt_of_ge (pow_le_pow_left₀ hr hle 2) hsq

/-- `indefiniteFoldMap` maps every open ball around `0 : ℝ⁴` onto a neighborhood of `0 : ℝ²`. -/
-- tier: T2
theorem indefiniteFoldMap_ball_nhds (r : ℝ) (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧
      Metric.ball (0 : EuclideanPlane) δ ⊆
        indefiniteFoldMap '' Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) r := by
  refine ⟨min (r / 2) (r ^ 2 / 4), lt_min (by positivity) (by positivity), ?_⟩
  intro w hw
  rw [Metric.mem_ball, dist_zero_right] at hw
  have hw_half : ‖w‖ < r / 2 := lt_of_lt_of_le hw (min_le_left _ _)
  have hw_sq4 : ‖w‖ < r ^ 2 / 4 := lt_of_lt_of_le hw (min_le_right _ _)
  have ha_le : |w 0| ≤ ‖w‖ := by simpa using (PiLp.norm_apply_le w (0 : Fin 2))
  have hb_le : |w 1| ≤ ‖w‖ := by simpa using (PiLp.norm_apply_le w (1 : Fin 2))
  have hb_sq : w 1 ^ 2 < r ^ 2 / 4 := by
    have hb_lt : |w 1| < r / 2 := lt_of_le_of_lt hb_le hw_half
    nlinarith [abs_nonneg (w 1), sq_abs (w 1)]
  by_cases ha : 0 ≤ w 0
  · refine ⟨vec4 (Real.sqrt (w 0)) 0 0 (w 1), ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right]
      refine norm_lt_of_sq_lt_sq hr.le ?_
      rw [norm_sq_vec4]
      simp only [vec4_zero, vec4_one, vec4_two, vec4_three, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, add_zero]
      rw [Real.sq_sqrt ha]
      have ha_lt : w 0 < r ^ 2 / 4 := lt_of_le_of_lt (le_trans (le_abs_self _) ha_le) hw_sq4
      linarith
    · refine ext_vec2 ?_ rfl
      simp [Real.sq_sqrt ha]
  · have ha_neg : w 0 < 0 := lt_of_not_ge ha
    have h2a_pos : 0 ≤ -2 * w 0 := by linarith
    refine ⟨vec4 0 (Real.sqrt (-2 * w 0)) 0 (w 1), ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right]
      refine norm_lt_of_sq_lt_sq hr.le ?_
      rw [norm_sq_vec4]
      simp only [vec4_zero, vec4_one, vec4_two, vec4_three, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_add]
      rw [Real.sq_sqrt h2a_pos]
      have hneg_a : -w 0 < r ^ 2 / 4 :=
        lt_of_le_of_lt (le_trans (neg_le_abs _) ha_le) hw_sq4
      linarith
    · refine ext_vec2 ?_ rfl
      have hsq_2 : Real.sqrt (-2 * w 0) ^ 2 = -2 * w 0 := Real.sq_sqrt h2a_pos
      simp only [indefiniteFoldMap_vec4, vec2_zero]
      rw [hsq_2]
      ring

/-- `wrinkledCuspMap` maps every open ball around `0 : ℝ⁴` onto a neighborhood of `0 : ℝ²`. -/
-- tier: T2
theorem wrinkledCuspMap_ball_nhds (r : ℝ) (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧
      Metric.ball (0 : EuclideanPlane) δ ⊆
        wrinkledCuspMap '' Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) r := by
  refine ⟨min (r / 2) (r ^ 2 / 4), lt_min (by positivity) (by positivity), ?_⟩
  intro w hw
  rw [Metric.mem_ball, dist_zero_right] at hw
  have hw_half : ‖w‖ < r / 2 := lt_of_lt_of_le hw (min_le_left _ _)
  have hw_sq4 : ‖w‖ < r ^ 2 / 4 := lt_of_lt_of_le hw (min_le_right _ _)
  have ha_le : |w 0| ≤ ‖w‖ := by simpa using (PiLp.norm_apply_le w (0 : Fin 2))
  have hb_le : |w 1| ≤ ‖w‖ := by simpa using (PiLp.norm_apply_le w (1 : Fin 2))
  have ha_sq : w 0 ^ 2 < r ^ 2 / 4 := by
    have ha_lt : |w 0| < r / 2 := lt_of_le_of_lt ha_le hw_half
    nlinarith [abs_nonneg (w 0), sq_abs (w 0)]
  by_cases hb : 0 ≤ w 1
  · refine ⟨vec4 (w 0) 0 (Real.sqrt (w 1)) 0, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right]
      refine norm_lt_of_sq_lt_sq hr.le ?_
      rw [norm_sq_vec4]
      simp only [vec4_zero, vec4_one, vec4_two, vec4_three, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, add_zero]
      rw [Real.sq_sqrt hb]
      have hb_lt : w 1 < r ^ 2 / 4 := lt_of_le_of_lt (le_trans (le_abs_self _) hb_le) hw_sq4
      linarith
    · refine ext_vec2 rfl ?_
      simp [Real.sq_sqrt hb]
  · have hb_neg : w 1 < 0 := lt_of_not_ge hb
    have hneg_b : 0 ≤ -w 1 := by linarith
    refine ⟨vec4 (w 0) 0 0 (Real.sqrt (-w 1)), ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right]
      refine norm_lt_of_sq_lt_sq hr.le ?_
      rw [norm_sq_vec4]
      simp only [vec4_zero, vec4_one, vec4_two, vec4_three, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, add_zero]
      rw [Real.sq_sqrt hneg_b]
      have hnb_lt : -w 1 < r ^ 2 / 4 :=
        lt_of_le_of_lt (le_trans (neg_le_abs _) hb_le) hw_sq4
      linarith
    · refine ext_vec2 rfl ?_
      simp [Real.sq_sqrt hneg_b]

/-- `realLefschetzMap` maps every open ball around `0 : ℝ⁴` onto a neighborhood of `0 : ℝ²`. -/
-- tier: T2
theorem realLefschetzMap_ball_nhds (r : ℝ) (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧
      Metric.ball (0 : EuclideanPlane) δ ⊆
        realLefschetzMap '' Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) r := by
  refine ⟨r ^ 2 / 2, by positivity, ?_⟩
  intro w hw
  rw [Metric.mem_ball, dist_zero_right] at hw
  set ρ := ‖w‖
  have hρ_sq : ρ ^ 2 = w 0 ^ 2 + w 1 ^ 2 := norm_sq_plane w
  have ha_sq : w 0 ^ 2 ≤ ρ ^ 2 := by nlinarith [sq_nonneg (w 1)]
  have ha_le : |w 0| ≤ ρ := by
    nlinarith [abs_nonneg (w 0), norm_nonneg w, sq_abs (w 0)]
  have hpa_nonneg : 0 ≤ (ρ + w 0) / 2 := by nlinarith [le_trans (neg_le_abs _) ha_le]
  have hma_nonneg : 0 ≤ (ρ - w 0) / 2 := by nlinarith [le_trans (le_abs_self _) ha_le]
  set u := Real.sqrt ((ρ + w 0) / 2)
  set v₀ := Real.sqrt ((ρ - w 0) / 2)
  have hu_sq : u ^ 2 = (ρ + w 0) / 2 := Real.sq_sqrt hpa_nonneg
  have hv_sq : v₀ ^ 2 = (ρ - w 0) / 2 := Real.sq_sqrt hma_nonneg
  have huv_sq : (2 * u * v₀) ^ 2 = w 1 ^ 2 := by
    calc
      (2 * u * v₀) ^ 2 = 4 * u ^ 2 * v₀ ^ 2 := by ring
      _ = 4 * ((ρ + w 0) / 2) * ((ρ - w 0) / 2) := by rw [hu_sq, hv_sq]
      _ = ρ ^ 2 - w 0 ^ 2 := by ring
      _ = w 1 ^ 2 := by linarith
  by_cases hb : 0 ≤ w 1
  · have huv : 2 * u * v₀ = w 1 := by
      have hpos : 0 ≤ 2 * u * v₀ := by positivity
      nlinarith [sq_nonneg (2 * u * v₀ - w 1)]
    refine ⟨vec4 u v₀ 0 0, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right]
      refine norm_lt_of_sq_lt_sq hr.le ?_
      rw [norm_sq_vec4]
      simp only [vec4_zero, vec4_one, vec4_two, vec4_three, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, add_zero]
      linarith
    · refine ext_vec2 ?_ ?_
      · simp only [realLefschetzMap_apply_zero, vec4_zero, vec4_one, vec4_two, vec4_three]
        rw [hu_sq, hv_sq]
        ring
      · simp only [realLefschetzMap_apply_one, vec4_zero, vec4_one, vec4_two, vec4_three]
        linarith
  · have hb_neg : w 1 < 0 := lt_of_not_ge hb
    have huv : 2 * u * v₀ = -w 1 := by
      have hpos : 0 ≤ 2 * u * v₀ := by positivity
      nlinarith [sq_nonneg (2 * u * v₀ + w 1)]
    refine ⟨vec4 u (-v₀) 0 0, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right]
      refine norm_lt_of_sq_lt_sq hr.le ?_
      rw [norm_sq_vec4]
      simp only [vec4_zero, vec4_one, vec4_two, vec4_three, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, add_zero]
      linarith
    · refine ext_vec2 ?_ ?_
      · simp only [realLefschetzMap_apply_zero, vec4_zero, vec4_one, vec4_two, vec4_three, neg_sq]
        rw [hu_sq, hv_sq]
        ring
      · simp only [realLefschetzMap_apply_one, vec4_zero, vec4_one, vec4_two, vec4_three]
        linarith

/-- If `f` is locally modeled at `p` on a model `model` that is open at `0` (sends every ball
around `0 : ℝ⁴` onto a set containing a ball around `model 0`), then `Set.range f ∈ 𝓝 (f p)`. -/
-- tier: T2
theorem mem_nhds_range_of_isLocallyModeledOn
    {E_M H_M E_B H_B M Base : Type*}
    [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    {I_M : ModelWithCorners ℝ E_M H_M}
    [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    {I_B : ModelWithCorners ℝ E_B H_B}
    [TopologicalSpace M] [ChartedSpace H_M M]
    [TopologicalSpace Base] [ChartedSpace H_B Base]
    {f : M → Base} {p : M} {model : EuclideanSpace ℝ (Fin 4) → EuclideanPlane}
    (hmodel : ∀ r : ℝ, 0 < r → ∃ δ : ℝ, 0 < δ ∧
      Metric.ball (model 0) δ ⊆ model '' Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) r)
    (hl : IsLocallyModeledOn I_M I_B f p model 0) :
    Set.range f ∈ 𝓝 (f p) := by
  obtain ⟨φ, ψ, hpφ, hfpψ, hφp, hψfp, hmodelEq⟩ := hl
  have h0_target : (0 : EuclideanSpace ℝ (Fin 4)) ∈ φ.target := by
    rw [← hφp]
    exact φ.map_source hpφ
  obtain ⟨r, hr, hball_r⟩ := Metric.isOpen_iff.mp φ.open_target 0 h0_target
  obtain ⟨δ, hδ, hball_δ⟩ := hmodel r hr
  have hpre_open : IsOpen (ψ.source ∩ ψ ⁻¹' Metric.ball (model 0) δ) := by
    rw [← ψ.toOpenPartialHomeomorph_source]
    exact ψ.toOpenPartialHomeomorph.isOpen_inter_preimage Metric.isOpen_ball
  refine Filter.mem_of_superset (hpre_open.mem_nhds ⟨hfpψ, ?_⟩) ?_
  · rw [Set.mem_preimage, hψfp]
    exact Metric.mem_ball_self hδ
  · rintro y ⟨hyψ, hy_ball⟩
    obtain ⟨z, hz_ball, hz_eq⟩ := hball_δ hy_ball
    have hz_target : z ∈ φ.target := hball_r hz_ball
    let q := φ.toPartialEquiv.symm z
    have hq_source : q ∈ φ.source := φ.map_target hz_target
    have hfq : f q ∈ ψ.source ∧ ψ (f q) = model (φ q) := hmodelEq q hq_source
    have hφq : φ q = z := φ.right_inv hz_target
    have hψeq : ψ (f q) = ψ y := by rw [hfq.2, hφq, hz_eq]
    have hfy : f q = y := ψ.toPartialEquiv.injOn hfq.1 hyψ hψeq
    exact ⟨q, hfy⟩

theorem range_indefiniteFoldMap_mem_nhds_of_isIndefiniteFoldAt
    {E_M H_M E_B H_B M Base : Type*}
    [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    {I_M : ModelWithCorners ℝ E_M H_M}
    [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    {I_B : ModelWithCorners ℝ E_B H_B}
    [TopologicalSpace M] [ChartedSpace H_M M]
    [TopologicalSpace Base] [ChartedSpace H_B Base]
    {f : M → Base} {p : M} (h : IsIndefiniteFoldAt I_M I_B f p) :
    Set.range f ∈ 𝓝 (f p) :=
  mem_nhds_range_of_isLocallyModeledOn
    (fun r hr ↦ by
      have hz : indefiniteFoldMap 0 = 0 := ext_vec2 (by simp) rfl
      simpa only [hz] using indefiniteFoldMap_ball_nhds r hr)
    h

theorem range_wrinkledCuspMap_mem_nhds_of_isWrinkledCuspAt
    {E_M H_M E_B H_B M Base : Type*}
    [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    {I_M : ModelWithCorners ℝ E_M H_M}
    [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    {I_B : ModelWithCorners ℝ E_B H_B}
    [TopologicalSpace M] [ChartedSpace H_M M]
    [TopologicalSpace Base] [ChartedSpace H_B Base]
    {f : M → Base} {p : M} (h : IsWrinkledCuspAt I_M I_B f p) :
    Set.range f ∈ 𝓝 (f p) :=
  mem_nhds_range_of_isLocallyModeledOn
    (fun r hr ↦ by
      have hz : wrinkledCuspMap 0 = 0 := ext_vec2 rfl (by simp)
      simpa only [hz] using wrinkledCuspMap_ball_nhds r hr)
    h

theorem range_realLefschetzMap_mem_nhds_of_isRealLefschetzAt
    {E_M H_M E_B H_B M Base : Type*}
    [NormedAddCommGroup E_M] [NormedSpace ℝ E_M] [TopologicalSpace H_M]
    {I_M : ModelWithCorners ℝ E_M H_M}
    [NormedAddCommGroup E_B] [NormedSpace ℝ E_B] [TopologicalSpace H_B]
    {I_B : ModelWithCorners ℝ E_B H_B}
    [TopologicalSpace M] [ChartedSpace H_M M]
    [TopologicalSpace Base] [ChartedSpace H_B Base]
    {f : M → Base} {p : M} (h : IsRealLefschetzAt I_M I_B f p) :
    Set.range f ∈ 𝓝 (f p) :=
  mem_nhds_range_of_isLocallyModeledOn
    (fun r hr ↦ by
      have hz : realLefschetzMap 0 = 0 := ext_vec2 (by simp) (by simp)
      simpa only [hz] using realLefschetzMap_ball_nhds r hr)
    h

/-- Global upper bound `‖s4ProjPlane q.1‖ ≤ 1` for every point `q : Sphere4`. -/
theorem norm_s4ProjPlane_le_one (q : Sphere4) : ‖s4ProjPlane q.1‖ ≤ 1 := by
  have hsplit := norm_sq_s4_split q
  have hsq : ‖s4ProjPlane q.1‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖s4ProjFiber q.1‖]
  nlinarith [norm_nonneg (s4ProjPlane q.1)]

/-- Every critical point `p` of `s4Fibration` satisfies `‖s4ProjPlane p.1‖ = 1`. -/
theorem norm_s4ProjPlane_eq_one_of_mem_criticalPoints {p : Sphere4}
    (hp : p ∈ criticalPoints (𝓡 4) (𝓡 2) s4Fibration) :
    ‖s4ProjPlane p.1‖ = 1 := by
  rw [criticalPoints_s4Fibration, Set.mem_ofPred_eq] at hp
  have hsplit := norm_sq_s4_split p
  rw [hp, norm_zero, zero_pow two_ne_zero, add_zero] at hsplit
  nlinarith [norm_nonneg (s4ProjPlane p.1)]

/-- For a definite-fold critical point `p` of `s4Fibration`, `Set.range s4Fibration` is NOT a
neighborhood of `s4Fibration p`. -/
-- tier: T2
theorem not_mem_nhds_range_s4Fibration {p : Sphere4}
    (hp : p ∈ criticalPoints (𝓡 4) (𝓡 2) s4Fibration) :
    Set.range s4Fibration ∉ 𝓝 (s4Fibration p) := by
  intro hnhds
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  have hcont := contMDiff_southPoleStereoInv.continuous.continuousAt (x := s4ProjPlane p.1)
  obtain ⟨η, hη, hη_dist⟩ := Metric.continuousAt_iff.mp hcont δ hδ
  let ε : ℝ := η / 2
  have hε_pos : 0 < ε := by positivity
  let w : EuclideanPlane := (1 + ε) • s4ProjPlane p.1
  have hp_norm : ‖s4ProjPlane p.1‖ = 1 := norm_s4ProjPlane_eq_one_of_mem_criticalPoints hp
  have hw_dist : dist w (s4ProjPlane p.1) < η := by
    rw [dist_eq_norm]
    have hsub : w - s4ProjPlane p.1 = ε • s4ProjPlane p.1 := by
      ext i
      simp only [w, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [hsub, norm_smul, Real.norm_of_nonneg hε_pos.le, hp_norm, mul_one]
    dsimp only [ε]
    linarith
  have hw_mem : southPoleStereoInv w ∈ Set.range s4Fibration :=
    hball (by
      rw [Metric.mem_ball]
      exact hη_dist hw_dist)
  obtain ⟨q, hq⟩ := hw_mem
  have hq_eq : s4ProjPlane q.1 = w := injective_southPoleStereoInv hq
  have hw_norm : ‖w‖ = 1 + ε := by
    simp only [w, norm_smul, Real.norm_of_nonneg (by linarith : 0 ≤ 1 + ε), hp_norm, mul_one]
  have hq_le : ‖s4ProjPlane q.1‖ ≤ 1 := norm_s4ProjPlane_le_one q
  rw [hq_eq, hw_norm] at hq_le
  linarith [hε_pos]

/-- **Gate G5.1 Definite-Fold Exclusion**: no critical point of `s4Fibration` satisfies
`IsIndefiniteFoldAt`. -/
theorem not_isIndefiniteFoldAt_s4Fibration {p : Sphere4}
    (hp : p ∈ criticalPoints (𝓡 4) (𝓡 2) s4Fibration) :
    ¬ IsIndefiniteFoldAt (𝓡 4) (𝓡 2) s4Fibration p :=
  fun h ↦ not_mem_nhds_range_s4Fibration hp
    (range_indefiniteFoldMap_mem_nhds_of_isIndefiniteFoldAt h)

/-- **Gate G5.1 Definite-Fold Exclusion**: no critical point of `s4Fibration` satisfies
`IsWrinkledCuspAt`. -/
theorem not_isWrinkledCuspAt_s4Fibration {p : Sphere4}
    (hp : p ∈ criticalPoints (𝓡 4) (𝓡 2) s4Fibration) :
    ¬ IsWrinkledCuspAt (𝓡 4) (𝓡 2) s4Fibration p :=
  fun h ↦ not_mem_nhds_range_s4Fibration hp (range_wrinkledCuspMap_mem_nhds_of_isWrinkledCuspAt h)

/-- **Gate G5.1 Definite-Fold Exclusion**: no critical point of `s4Fibration` satisfies
`IsRealLefschetzAt`. -/
theorem not_isRealLefschetzAt_s4Fibration {p : Sphere4}
    (hp : p ∈ criticalPoints (𝓡 4) (𝓡 2) s4Fibration) :
    ¬ IsRealLefschetzAt (𝓡 4) (𝓡 2) s4Fibration p :=
  fun h ↦ not_mem_nhds_range_s4Fibration hp (range_realLefschetzMap_mem_nhds_of_isRealLefschetzAt h)

/-- `s4Fibration` does not admit a `BrokenLefschetzFibration` lift (`s4CriticalPoint` is a
definite fold). -/
theorem not_brokenLefschetzFibration_s4Fibration
    (B : BrokenLefschetzFibration (𝓡 4) Sphere4 (𝓡 2) Sphere2 Sphere2) :
    B.toFun ≠ s4Fibration := by
  intro hEq
  have hcrit : s4CriticalPoint ∈ criticalPoints (𝓡 4) (𝓡 2) B.toFun := by
    rw [hEq]
    exact s4CriticalPoint_mem_criticalPoints
  rcases B.singularities_broken_lefschetz s4CriticalPoint hcrit with hlef | hfold
  · rw [hEq] at hlef
    exact not_isRealLefschetzAt_s4Fibration s4CriticalPoint_mem_criticalPoints hlef
  · rw [hEq] at hfold
    exact not_isIndefiniteFoldAt_s4Fibration s4CriticalPoint_mem_criticalPoints hfold

/-- `s4Fibration` does not admit a `PurelyWrinkledFibration` lift (`s4CriticalPoint` is a
definite fold). -/
theorem not_purelyWrinkledFibration_s4Fibration
    (P : PurelyWrinkledFibration (𝓡 4) Sphere4 (𝓡 2) Sphere2 Sphere2) :
    P.toFun ≠ s4Fibration := by
  intro hEq
  have hcrit : s4CriticalPoint ∈ criticalPoints (𝓡 4) (𝓡 2) P.toFun := by
    rw [hEq]
    exact s4CriticalPoint_mem_criticalPoints
  rcases P.singularities_purely_wrinkled s4CriticalPoint hcrit with hfold | hcusp
  · rw [hEq] at hfold
    exact not_isIndefiniteFoldAt_s4Fibration s4CriticalPoint_mem_criticalPoints hfold
  · rw [hEq] at hcusp
    exact not_isWrinkledCuspAt_s4Fibration s4CriticalPoint_mem_criticalPoints hcusp

end DefiniteFoldExclusion

end S4TuringPoisson
