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

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import S4TuringPoisson.Fibration.S4Fibration
public import S4TuringPoisson.Fibration.WrinkledGeneral4Manifold
public import S4TuringPoisson.Poisson.JacobianPoisson
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
public import TauCeti.Geometry.Manifold.Orientation.CoordinateBall
public import TauCeti.Geometry.Manifold.Orientation.TopForm

/-!
# Unconditional Local Regular-Disk Fibration on Closed Oriented 4-Manifolds (`L-R3`, Track B)

This file implements Deliverable `L-R3` (Track B) together with the `SC-R1` / `SC-R2` separation
theorems, proving that every nonempty compact Hausdorff smooth 4-manifold `M` equipped with a
positive volume 4-form `V_M : PositiveVolumeForm (𝓡 4) M` admits an inhabitant of
`AdmitsRegularDiskFibration M` with zero additional geometric typeclasses, while separating this
local coordinate-ball construction sharply from genuine wrinkled / broken Lefschetz fibrations
(`AdmitsWrinkledOrBrokenLefschetzFibration M`):

1. **West-Pole 4D Inverse Stereographic Chart (`stereo4Inv`, `stereo4Diffeomorph`)**:
   - Identifies `EuclideanSpace ℝ (Fin 4)` diffeomorphically with `Sphere4 \ {s4WestPole}` where
     `s4WestPole = (-1, 0, 0, 0, 0) ∉ s4PreimageOpen`.
   - Defines the nowhere-vanishing pulled-back volume 4-form `stereo4PullbackVolume` on `ℝ⁴`.

2. **Orientation-Preserving Top-Form Pullback & Coordinate Ball (`exists_pos_smul_mpullback_...`)**:
   - Converts `TauCeti.Manifold.Orientation.IsOrientationPreservingAt` between top-form
     orientations into pointwise positive scalar proportionality `f^* φ' = c • φ` (`c > 0`).
3. **Bumped Stereographic Local Fibration (`closedManifoldLocalMap`,
   `closedManifoldRegularDiskFibration`)**:
   - Obtains an orientation-preserving smooth open embedding `e : ℝ⁴ → M` via
     `exists_isOpenEmbedding_isLocalDiffeomorph_isOrientationPreservingAt`.
   - Blends `P(u) = s4ProjPlane (stereo4Inv u)` via a smooth radial `ContDiffBump` (`rIn = 4`,
     `rOut = 9 / 2`) toward `vec2 (-1) 0` and composes with `southPoleStereoInv`, extending
     smoothly outside `e (closedBall 0 (9 / 2))` by the constant `southPoleStereoInv (vec2 (-1) 0)`
     (disjoint from `s4BaseRegion`).
   - Proves `closedManifoldLocalMap ⁻¹' s4BaseRegion = (e ∘ stereo4Chart) '' s4PreimageOpen` and
     deduces `AdmitsRegularDiskFibration.ofPositiveVolumeForm`.
4. **Track B Separation (`SC-R2`)**:
   - Proves `criticalPoints` of `closedManifoldRegularDiskFibration ch` has nonempty interior (since
     `closedManifoldLocalMap ch` is constant on the nonempty open exterior
     `ch.emb '' {u | 5 < ‖u‖}`), so its Jacobian–Poisson structure satisfies
     `¬ π_f.IsGenericallyRankTwo` and cannot underlie any
     `AdmitsWrinkledOrBrokenLefschetzFibration M`.
-/

@[expose] public section

open Filter Function Metric Module Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace S4TuringPoisson

/-! ## 1. West-Pole 4D Stereographic Chart on $S^4 \subset \mathbb{R}^5$ -/

section WestPoleStereo4

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

/-- Norm-squared expansion on `EuclideanSpace ℝ (Fin 4)` (local helper). -/
private theorem norm_sq_r4 (u : EuclideanSpace ℝ (Fin 4)) :
    ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_four]
  simp [Real.norm_eq_abs, sq_abs]

/-- West pole `(-1, 0, 0, 0, 0) ∈ Sphere4`. -/
noncomputable def s4WestPole : Sphere4 :=
  ⟨vec5 (-1) 0 0 0 0, by
    rw [mem_sphere_zero_iff_norm]
    have hsq : ‖vec5 (-1) 0 0 0 0‖ ^ 2 = 1 := by rw [norm_sq_vec5]; norm_num
    nlinarith [norm_nonneg (vec5 (-1) 0 0 0 0)]⟩

/-- Open punctured 4-sphere `Sphere4 \ {s4WestPole}`. -/
noncomputable abbrev s4PuncturedWest : Opens Sphere4 :=
  ⟨{s4WestPole}ᶜ, isOpen_compl_singleton⟩

/-- Ambient formula for west-pole 4D inverse stereographic projection `ℝ⁴ → ℝ⁵`:
`u ↦ ((4 - ‖u‖²), 4 u₀, 4 u₁, 4 u₂, 4 u₃) / (‖u‖² + 4)`. -/
noncomputable def stereo4Raw (u : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 5) :=
  let s := u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2
  let d := s + 4
  vec5 ((4 - s) / d) (4 * u 0 / d) (4 * u 1 / d) (4 * u 2 / d) (4 * u 3 / d)

theorem stereo4Raw_mem_sphere (u : EuclideanSpace ℝ (Fin 4)) :
    stereo4Raw u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have hden : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 + 4 ≠ 0 := by positivity
  have hsq : ‖stereo4Raw u‖ ^ 2 = 1 := by
    rw [norm_sq_vec5]
    simp only [stereo4Raw, vec5_zero, vec5_one, vec5_two, vec5_three, vec5_four]
    field_simp [hden]
    ring
  nlinarith [norm_nonneg (stereo4Raw u)]

/-- Smoothness (`ContDiff ℝ ∞`) of `stereo4Raw : ℝ⁴ → ℝ⁵`. -/
theorem contDiff_stereo4Raw : ContDiff ℝ ∞ stereo4Raw := by
  have hu (i : Fin 4) : ContDiff ℝ ∞ (fun u : EuclideanSpace ℝ (Fin 4) ↦ u i) :=
    (euclidProj i).contDiff
  have hs : ContDiff ℝ ∞ (fun u : EuclideanSpace ℝ (Fin 4) ↦
      u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2) :=
    ((((hu 0).pow 2).add ((hu 1).pow 2)).add ((hu 2).pow 2)).add ((hu 3).pow 2)
  have hd : ContDiff ℝ ∞ (fun u : EuclideanSpace ℝ (Fin 4) ↦
      u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 + 4) :=
    hs.add contDiff_const
  have hne : ∀ u : EuclideanSpace ℝ (Fin 4),
      u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 + 4 ≠ 0 := fun u ↦ by positivity
  exact contDiff_vec5
    ((contDiff_const.sub hs).div hd hne)
    ((contDiff_const.mul (hu 0)).div hd hne)
    ((contDiff_const.mul (hu 1)).div hd hne)
    ((contDiff_const.mul (hu 2)).div hd hne)
    ((contDiff_const.mul (hu 3)).div hd hne)

/-- West-pole inverse stereographic projection `ℝ⁴ → Sphere4`. -/
noncomputable def stereo4Inv (u : EuclideanSpace ℝ (Fin 4)) : Sphere4 :=
  Set.codRestrict stereo4Raw (Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1)
    stereo4Raw_mem_sphere u

@[simp]
theorem coe_stereo4Inv (u : EuclideanSpace ℝ (Fin 4)) :
    (stereo4Inv u : EuclideanSpace ℝ (Fin 5)) = stereo4Raw u :=
  rfl

/-- `stereo4Inv : ℝ⁴ → Sphere4` is globally $C^\infty$ smooth. -/
theorem contMDiff_stereo4Inv : ContMDiff (𝓡 4) (𝓡 4) ∞ stereo4Inv :=
  contDiff_stereo4Raw.contMDiff.codRestrict_sphere stereo4Raw_mem_sphere

theorem stereo4Inv_ne_westPole (u : EuclideanSpace ℝ (Fin 4)) :
    stereo4Inv u ≠ s4WestPole := by
  intro h
  have h0 := congrArg (fun x : Sphere4 ↦ x.1 0) h
  simp only [coe_stereo4Inv, stereo4Raw, vec5_zero, s4WestPole] at h0
  have hden : 0 < u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 + 4 := by positivity
  rw [div_eq_iff hden.ne'] at h0
  linarith

theorem one_add_coord0_pos_of_ne_westPole {x : Sphere4} (hx : x ≠ s4WestPole) :
    0 < 1 + x.1 0 := by
  have hnorm : x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2 + x.1 3 ^ 2 + x.1 4 ^ 2 = 1 := by
    rw [← norm_sq_vec5, mem_sphere_zero_iff_norm.mp x.2]
    norm_num
  have hge : 0 ≤ 1 + x.1 0 := by
    nlinarith [sq_nonneg (x.1 1), sq_nonneg (x.1 2), sq_nonneg (x.1 3), sq_nonneg (x.1 4),
      sq_nonneg (x.1 0 + 1)]
  refine lt_of_le_of_ne hge fun hzero ↦ hx ?_
  have hx0 : x.1 0 = -1 := by linarith
  have hx1 : x.1 1 = 0 := by
    nlinarith [sq_nonneg (x.1 2), sq_nonneg (x.1 3), sq_nonneg (x.1 4)]
  have hx2 : x.1 2 = 0 := by
    nlinarith [sq_nonneg (x.1 1), sq_nonneg (x.1 3), sq_nonneg (x.1 4)]
  have hx3 : x.1 3 = 0 := by
    nlinarith [sq_nonneg (x.1 1), sq_nonneg (x.1 2), sq_nonneg (x.1 4)]
  have hx4 : x.1 4 = 0 := by
    nlinarith [sq_nonneg (x.1 1), sq_nonneg (x.1 2), sq_nonneg (x.1 3)]
  exact Subtype.ext (ext_vec5 hx0 hx1 hx2 hx3 hx4)

/-- Forward west-pole stereographic coordinate map `Sphere4 → ℝ⁴`. -/
noncomputable def stereo4Chart (x : Sphere4) : EuclideanSpace ℝ (Fin 4) :=
  let d := 1 + x.1 0
  vec4 (2 * x.1 1 / d) (2 * x.1 2 / d) (2 * x.1 3 / d) (2 * x.1 4 / d)

@[simp]
theorem stereo4Chart_inv (u : EuclideanSpace ℝ (Fin 4)) :
    stereo4Chart (stereo4Inv u) = u := by
  have hden : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 + 4 ≠ 0 := by positivity
  refine ext_vec4 ?_ ?_ ?_ ?_
  · simp only [stereo4Chart, coe_stereo4Inv, stereo4Raw, vec4_zero, vec5_zero, vec5_one]
    field_simp [hden]; ring
  · simp only [stereo4Chart, coe_stereo4Inv, stereo4Raw, vec4_one, vec5_zero, vec5_two]
    field_simp [hden]; ring
  · simp only [stereo4Chart, coe_stereo4Inv, stereo4Raw, vec4_two, vec5_zero, vec5_three]
    field_simp [hden]; ring
  · simp only [stereo4Chart, coe_stereo4Inv, stereo4Raw, vec4_three, vec5_zero, vec5_four]
    field_simp [hden]; ring

theorem injective_stereo4Inv : Function.Injective stereo4Inv :=
  Function.LeftInverse.injective stereo4Chart_inv

theorem stereo4Inv_chart {x : Sphere4} (hx : x ≠ s4WestPole) :
    stereo4Inv (stereo4Chart x) = x := by
  have h1x : 1 + x.1 0 ≠ 0 := (one_add_coord0_pos_of_ne_westPole hx).ne'
  have hnorm : x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2 + x.1 3 ^ 2 + x.1 4 ^ 2 = 1 := by
    rw [← norm_sq_vec5, mem_sphere_zero_iff_norm.mp x.2]
    norm_num
  let u := stereo4Chart x
  have hu_den : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 + 4 = 8 / (1 + x.1 0) := by
    simp only [u, stereo4Chart, vec4_zero, vec4_one, vec4_two, vec4_three]
    field_simp [h1x]
    linear_combination 4 * hnorm
  apply Subtype.ext
  refine ext_vec5 ?_ ?_ ?_ ?_ ?_
  · change (4 - (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2)) /
        (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 + 4) = x.1 0
    have hu_sum : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 = 8 / (1 + x.1 0) - 4 := by
      linarith [hu_den]
    rw [hu_den, hu_sum]
    field_simp [h1x]
    ring
  · change 4 * u 0 / (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 + 4) = x.1 1
    rw [hu_den]; simp only [u, stereo4Chart, vec4_zero]; field_simp [h1x]; ring
  · change 4 * u 1 / (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 + 4) = x.1 2
    rw [hu_den]; simp only [u, stereo4Chart, vec4_one]; field_simp [h1x]; ring
  · change 4 * u 2 / (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 + 4) = x.1 3
    rw [hu_den]; simp only [u, stereo4Chart, vec4_two]; field_simp [h1x]; ring
  · change 4 * u 3 / (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 + 4) = x.1 4
    rw [hu_den]; simp only [u, stereo4Chart, vec4_three]; field_simp [h1x]; ring

/-- Smooth diffeomorphism `ℝ⁴ ≃ₘ⟮𝓡 4, 𝓡 4⟯ (Sphere4 \ {s4WestPole})`. -/
noncomputable def stereo4Diffeomorph :
    EuclideanSpace ℝ (Fin 4) ≃ₘ⟮𝓡 4, 𝓡 4⟯ s4PuncturedWest where
  toFun u := ⟨stereo4Inv u, stereo4Inv_ne_westPole u⟩
  invFun x := stereo4Chart x.1
  left_inv u := stereo4Chart_inv u
  right_inv x := Subtype.ext (stereo4Inv_chart x.2)
  contMDiff_toFun :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff s4PuncturedWest _).mp contMDiff_stereo4Inv
  contMDiff_invFun := by
    have hcoe : ContMDiff (𝓡 4) 𝓘(ℝ, EuclideanSpace ℝ (Fin 5)) ∞
        (fun x : s4PuncturedWest ↦ (x.1 : EuclideanSpace ℝ (Fin 5))) :=
      contMDiff_coe_sphere.comp contMDiff_subtype_val
    have hc (i : Fin 5) : ContMDiff (𝓡 4) 𝓘(ℝ, ℝ) ∞ (fun x : s4PuncturedWest ↦ x.1.1 i) :=
      (euclidProj i).contDiff.contMDiff.comp hcoe
    have hinv : ContMDiff (𝓡 4) 𝓘(ℝ, ℝ) ∞ (fun x : s4PuncturedWest ↦ (1 + x.1.1 0)⁻¹) := by
      intro x
      have h1x : 1 + x.1.1 0 ≠ 0 := (one_add_coord0_pos_of_ne_westPole x.2).ne'
      have hadd : ContMDiffAt (𝓡 4) 𝓘(ℝ, ℝ) ∞ (fun y : s4PuncturedWest ↦ 1 + y.1.1 0) x :=
        (contDiff_const.add contDiff_id).contMDiff.contMDiffAt.comp x (hc 0).contMDiffAt
      exact (contDiffAt_inv ℝ h1x).contMDiffAt.comp x hadd
    have hmul2 : ContDiff ℝ ∞ (fun q : ℝ × ℝ ↦ (2 * q.1) * q.2) :=
      (contDiff_const.mul contDiff_fst).mul contDiff_snd
    have hdiv (j : Fin 5) : ContMDiff (𝓡 4) 𝓘(ℝ, ℝ) ∞
        (fun x : s4PuncturedWest ↦ 2 * x.1.1 j / (1 + x.1.1 0)) := by
      have heq : (fun x : s4PuncturedWest ↦ 2 * x.1.1 j / (1 + x.1.1 0)) =
          (fun q : ℝ × ℝ ↦ (2 * q.1) * q.2) ∘
            fun x : s4PuncturedWest ↦ (x.1.1 j, (1 + x.1.1 0)⁻¹) := by
        funext x; simp [div_eq_mul_inv]
      rw [heq]
      exact hmul2.contMDiff.comp ((hc j).prodMk_space hinv)
    have hpi : ContMDiff (𝓡 4) 𝓘(ℝ, Fin 4 → ℝ) ∞
        (fun x : s4PuncturedWest ↦
          ![2 * x.1.1 1 / (1 + x.1.1 0), 2 * x.1.1 2 / (1 + x.1.1 0),
            2 * x.1.1 3 / (1 + x.1.1 0), 2 * x.1.1 4 / (1 + x.1.1 0)]) := by
      refine contMDiff_pi_module_iff.mpr fun i ↦ ?_
      fin_cases i
      · exact hdiv 1
      · exact hdiv 2
      · exact hdiv 3
      · exact hdiv 4
    exact (EuclideanSpace.equiv (Fin 4) ℝ).symm.contDiff.contMDiff.comp hpi

theorem isLocalDiffeomorph_stereo4Inv : IsLocalDiffeomorph (𝓡 4) (𝓡 4) ∞ stereo4Inv :=
  fun u ↦ (stereo4Diffeomorph.isLocalDiffeomorph u).comp
    (hg := TauCeti.isLocalDiffeomorph_subtype_val (stereo4Diffeomorph u))

theorem isOpenEmbedding_stereo4Inv : Topology.IsOpenEmbedding stereo4Inv :=
  s4PuncturedWest.2.isOpenEmbedding_subtypeVal.comp
    stereo4Diffeomorph.toHomeomorph.isOpenEmbedding

/-- Pulled-back nowhere-vanishing smooth 4-form `stereo4Inv^* S4VolumeForm` on `ℝ⁴`. -/
noncomputable def stereo4PullbackVolume :
    TauCeti.SmoothForm (𝓡 4) (EuclideanSpace ℝ (Fin 4)) ℝ 4 :=
  TauCeti.SmoothForm.mpullback stereo4Inv contMDiff_stereo4Inv S4VolumeForm

theorem stereo4PullbackVolume_ne_zero (u : EuclideanSpace ℝ (Fin 4)) :
    stereo4PullbackVolume.1 u ≠ 0 := by
  rw [stereo4PullbackVolume, TauCeti.SmoothForm.coe_mpullback]
  exact fun hzero ↦ S4VolumeForm_ne_zero (stereo4Inv u)
    (((isLocalDiffeomorph_stereo4Inv u).mpullback_apply_eq_zero_iff (by simp)).mp hzero)

end WestPoleStereo4

/-! ## 2. Orientation-Preserving Coordinate Ball & Positive Top-Form Pullback -/

section OrientationPullback

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

/-- **Top-Form Orientation Pullback Equivalence**: if `f : M → M'` preserves the orientations
`ofTopForm hk φ ...` and `ofTopForm hk' φ' ...` at `x`, then `f^* φ'` at `x` equals a strictly
positive scalar multiple `c • φ_x` (`c > 0`). -/
-- tier: T2
theorem exists_pos_smul_mpullback_of_isOrientationPreservingAt_ofTopForm
    {E H M E' H' M' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    {k : ℕ} (hk : Module.finrank ℝ E = k) (hk' : Module.finrank ℝ E' = k)
    {φ : TauCeti.SmoothForm I M ℝ k} (h0 : ∀ z, φ.1 z ≠ 0)
    {φ' : TauCeti.SmoothForm I' M' ℝ k} (h0' : ∀ z, φ'.1 z ≠ 0)
    {f : M → M'} (hf : ContMDiff I I' ∞ f) {x : M}
    (hpres : TauCeti.Manifold.Orientation.IsOrientationPreservingAt
      (TauCeti.Manifold.Orientation.ofTopForm hk φ.1 (φ.isSmoothForm.of_le bot_le) h0)
      (TauCeti.Manifold.Orientation.ofTopForm hk' φ'.1 (φ'.isSmoothForm.of_le bot_le) h0') f x) :
    ∃ c : ℝ, 0 < c ∧ (TauCeti.SmoothForm.mpullback f hf φ').1 x = c • φ.1 x := by
  obtain ⟨eL, heL, hmap⟩ :=
    (TauCeti.Manifold.Orientation.isOrientationPreservingAt_iff _ _ _ _).mp hpres
  let b : Module.Basis (Fin k) ℝ (TangentSpace I x) :=
    Module.finBasisOfFinrankEq ℝ (TangentSpace I x) hk
  let b' : Module.Basis (Fin k) ℝ (TangentSpace I' (f x)) := b.map eL.toLinearEquiv
  have hb_ne : φ.1 x b ≠ 0 := ((φ.1 x).map_basis_ne_zero_iff b).mpr (h0 x)
  have hb'_ne : φ'.1 (f x) b' ≠ 0 := ((φ'.1 (f x)).map_basis_ne_zero_iff b').mpr (h0' (f x))
  have hb'_orient :
      b'.orientation = _root_.Orientation.map (Fin k) eL.toLinearEquiv b.orientation :=
    b.orientation_map eL.toLinearEquiv
  have hpos_iff : 0 < φ'.1 (f x) b' ↔ 0 < φ.1 x b := by
    rw [← TauCeti.Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff hk'
        (φ'.isSmoothForm.of_le bot_le) h0' b',
      ← TauCeti.Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff hk
        (φ.isSmoothForm.of_le bot_le) h0 b,
      hb'_orient, ← hmap]
    exact ⟨fun h ↦ (_root_.Orientation.map (Fin k) eL.toLinearEquiv).injective h,
      fun h ↦ by rw [h]⟩
  have hc_pos : 0 < φ'.1 (f x) b' / φ.1 x b := by
    rcases lt_or_gt_of_ne hb_ne with hneg | hpos
    · have hneg' : φ'.1 (f x) b' < 0 :=
        lt_of_le_of_ne (not_lt.mp fun h ↦ not_lt_of_gt hneg (hpos_iff.mp h)) hb'_ne
      exact div_pos_of_neg_of_neg hneg' hneg
    · exact div_pos (hpos_iff.mpr hpos) hpos
  refine ⟨φ'.1 (f x) b' / φ.1 x b, hc_pos, ?_⟩
  ext v
  rw [TauCeti.SmoothForm.mpullback_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    ContinuousAlternatingMap.apply_eq_det_mul (φ'.1 (f x)) b' (fun i ↦ mfderiv I I' f x (v i)),
    ContinuousAlternatingMap.apply_eq_det_mul (φ.1 x) b v]
  have hdet : b'.det (fun i ↦ mfderiv I I' f x (v i)) = b.det v := by
    have hvec : (fun i ↦ mfderiv I I' f x (v i)) = fun i ↦ eL (v i) := by
      funext i; rw [← heL]; rfl
    rw [hvec, Module.Basis.det_apply, Module.Basis.det_apply]
    congr 1
    ext i j
    simp [b', Module.Basis.toMatrix_apply]
  rw [hdet]
  field_simp [hb_ne]

/-- Packaged orientation-preserving smooth coordinate ball `e : ℝ⁴ → M` centered in `M` with
orientation pulled back from `stereo4PullbackVolume`. -/
structure ClosedManifoldChart (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M]
    [MeasurableSpace M] [BorelSpace M] (V_M : PositiveVolumeForm (𝓡 4) M) where
  /-- Smooth open embedding `ℝ⁴ → M`. -/
  emb : EuclideanSpace ℝ (Fin 4) → M
  /-- Topological open embedding property of `emb`. -/
  isOpenEmbedding : Topology.IsOpenEmbedding emb
  /-- Global smooth local diffeomorphism property of `emb`. -/
  isLocalDiffeomorph : IsLocalDiffeomorph (𝓡 4) (𝓡 4) ∞ emb
  /-- Positive pullback proportionality with `stereo4PullbackVolume` at every point `u : ℝ⁴`. -/
  pos_cooriented : ∀ u : EuclideanSpace ℝ (Fin 4), ∃ c : ℝ, 0 < c ∧
    (TauCeti.SmoothForm.mpullback emb isLocalDiffeomorph.contMDiff V_M.Ω).1 u =
      c • stereo4PullbackVolume.1 u

/-- Construct a `ClosedManifoldChart` on any nonempty smooth 4-manifold `(M, V_M)`. -/
-- tier: T2
noncomputable def closedManifoldChart (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [Nonempty M] (V_M : PositiveVolumeForm (𝓡 4) M) :
    ClosedManifoldChart M V_M := by
  let o_stereo := TauCeti.Manifold.Orientation.ofTopForm (I := 𝓡 4) finrank_euclideanSpace_fin
    stereo4PullbackVolume.1 (stereo4PullbackVolume.isSmoothForm.of_le bot_le)
    stereo4PullbackVolume_ne_zero
  let o_M := TauCeti.Manifold.Orientation.ofTopForm (I := 𝓡 4) finrank_euclideanSpace_fin
    V_M.Ω.1 (V_M.Ω.isSmoothForm.of_le bot_le) V_M.Ω_ne_zero
  have hex :=
    TauCeti.Manifold.Orientation.exists_isOpenEmbedding_isLocalDiffeomorph_isOrientationPreservingAt
      o_stereo o_M (Classical.arbitrary M)
  let e := Classical.choose hex
  have he_spec := Classical.choose_spec hex
  have he_emb : Topology.IsOpenEmbedding e := he_spec.2.1
  have he_loc : IsLocalDiffeomorph (𝓡 4) (𝓡 4) ∞ e := he_spec.2.2.1
  have he_orient : ∀ u, o_stereo.IsOrientationPreservingAt o_M e u := he_spec.2.2.2
  refine ⟨e, he_emb, he_loc, fun u ↦ ?_⟩
  exact exists_pos_smul_mpullback_of_isOrientationPreservingAt_ofTopForm
    (k := 4) finrank_euclideanSpace_fin finrank_euclideanSpace_fin
    stereo4PullbackVolume_ne_zero V_M.Ω_ne_zero he_loc.contMDiff (he_orient u)

/-- Smooth diffeomorphism `ℝ⁴ ≃ₘ⟮𝓡 4, 𝓡 4⟯ ch.isLocalDiffeomorph.image` induced by `ch.emb`. -/
noncomputable def ClosedManifoldChart.diffeo {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M]
    [MeasurableSpace M] [BorelSpace M] {V_M : PositiveVolumeForm (𝓡 4) M}
    (ch : ClosedManifoldChart M V_M) :
    EuclideanSpace ℝ (Fin 4) ≃ₘ⟮𝓡 4, 𝓡 4⟯ ch.isLocalDiffeomorph.image :=
  ch.isLocalDiffeomorph.diffeomorphOfInjective ch.isOpenEmbedding.injective

@[simp]
theorem ClosedManifoldChart.apply_diffeo_symm {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M]
    [MeasurableSpace M] [BorelSpace M] {V_M : PositiveVolumeForm (𝓡 4) M}
    (ch : ClosedManifoldChart M V_M) {m : M} (hm : m ∈ Set.range ch.emb) :
    ch.emb (ch.diffeo.symm ⟨m, hm⟩) = m :=
  ch.isLocalDiffeomorph.apply_diffeomorphOfInjective_symm ch.isOpenEmbedding.injective ⟨m, hm⟩

@[simp]
theorem ClosedManifoldChart.diffeo_symm_apply {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M]
    [MeasurableSpace M] [BorelSpace M] {V_M : PositiveVolumeForm (𝓡 4) M}
    (ch : ClosedManifoldChart M V_M) (u : EuclideanSpace ℝ (Fin 4)) :
    ch.diffeo.symm ⟨ch.emb u, ⟨u, rfl⟩⟩ = u := by
  exact ch.isOpenEmbedding.injective (ch.apply_diffeo_symm ⟨u, rfl⟩)

end OrientationPullback

/-! ## 3. Bumped Stereographic Local Map and Smooth Gluing onto $M$ -/

section LocalBumpedFibration

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

/-- Smooth radial bump function on `ℝ⁴` equal to `1` on `closedBall 0 4` and supported inside
`ball 0 (9 / 2)`. -/
noncomputable def localRadialBump : ContDiffBump (0 : EuclideanSpace ℝ (Fin 4)) where
  rIn := 4
  rOut := 9 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- Blended planar map `P_tilde(u) = χ(u) • s4ProjPlane(stereo4Inv u) + (1 - χ(u)) • (-1, 0)`. -/
noncomputable def localPlaneBlend (u : EuclideanSpace ℝ (Fin 4)) : EuclideanPlane :=
  localRadialBump u • s4ProjPlane (stereo4Inv u).1 + (1 - localRadialBump u) • vec2 (-1) 0

/-- Smoothness (`ContDiff ℝ ∞`) of `localPlaneBlend : ℝ⁴ → ℝ²`. -/
theorem contDiff_localPlaneBlend : ContDiff ℝ ∞ localPlaneBlend := by
  have hχ : ContDiff ℝ ∞ (fun u : EuclideanSpace ℝ (Fin 4) ↦ localRadialBump u) :=
    localRadialBump.contDiff (n := ⊤)
  have hP : ContDiff ℝ ∞ (fun u : EuclideanSpace ℝ (Fin 4) ↦ s4ProjPlane (stereo4Inv u).1) :=
    s4ProjPlane.contDiff.comp contDiff_stereo4Raw
  exact (hχ.smul hP).add ((contDiff_const.sub hχ).smul contDiff_const)

/-- Local map on `ℝ⁴ → Sphere2` matching `s4Fibration ∘ stereo4Inv` on `closedBall 0 4` and
constant `southPoleStereoInv (vec2 (-1) 0)` outside `ball 0 (9 / 2)`. -/
noncomputable def localBallMap (u : EuclideanSpace ℝ (Fin 4)) : Sphere2 :=
  southPoleStereoInv (localPlaneBlend u)

theorem contMDiff_localBallMap : ContMDiff (𝓡 4) (𝓡 2) ∞ localBallMap :=
  contMDiff_southPoleStereoInv.comp contDiff_localPlaneBlend.contMDiff

theorem localBallMap_eq_s4Fibration_of_norm_le_four {u : EuclideanSpace ℝ (Fin 4)}
    (hu : ‖u‖ ≤ 4) :
    localBallMap u = s4Fibration (stereo4Inv u) := by
  have hmem : u ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) 4 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hu
  have h1 : localRadialBump u = 1 := localRadialBump.one_of_mem_closedBall hmem
  simp [localBallMap, localPlaneBlend, h1, s4Fibration]

theorem localBallMap_eq_const_of_notMem_closedBall {u : EuclideanSpace ℝ (Fin 4)}
    (hu : u ∉ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) (9 / 2)) :
    localBallMap u = southPoleStereoInv (vec2 (-1) 0) := by
  have hnot_ball : u ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) (9 / 2) :=
    fun hb ↦ hu (Metric.ball_subset_closedBall hb)
  have hnot_supp : u ∉ Function.support (⇑localRadialBump) := by
    rw [localRadialBump.support_eq]
    exact hnot_ball
  have h0 : localRadialBump u = 0 := Function.notMem_support.mp hnot_supp
  simp [localBallMap, localPlaneBlend, h0]

/-- Crucially: if `‖s4ProjPlane (stereo4Inv u).1‖ < 1 / 2`, then `‖u‖ < 4`. -/
theorem norm_lt_four_of_norm_proj_lt_half {u : EuclideanSpace ℝ (Fin 4)}
    (hp : ‖s4ProjPlane (stereo4Inv u).1‖ < 1 / 2) : ‖u‖ < 4 := by
  have hle0 : |s4ProjPlane (stereo4Inv u).1 0| ≤ ‖s4ProjPlane (stereo4Inv u).1‖ := by
    simpa using (PiLp.norm_apply_le (s4ProjPlane (stereo4Inv u).1) (0 : Fin 2))
  have hcoord : -1 / 2 < (stereo4Inv u).1 0 := by
    have hval : s4ProjPlane (stereo4Inv u).1 0 = (stereo4Inv u).1 0 := rfl
    linarith [(neg_le_abs _).trans hle0]
  have hden : 0 < u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 + 4 := by positivity
  have hnum : (stereo4Inv u).1 0 =
      (4 - (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2)) /
        (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 + 4) := rfl
  rw [hnum] at hcoord
  have hlt16 : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 < 12 := by
    have hmul := (lt_div_iff₀ hden).mp hcoord
    linarith
  rw [← norm_sq_r4] at hlt16
  nlinarith [norm_nonneg u]

/-- If `4 ≤ ‖u‖`, then `1 / 2 ≤ ‖localPlaneBlend u‖` (in fact `(localPlaneBlend u) 0 ≤ -3 / 5`),
so `localBallMap u ∉ s4BaseRegion`. -/
theorem norm_localPlaneBlend_ge_half_of_four_le {u : EuclideanSpace ℝ (Fin 4)}
    (hu : 4 ≤ ‖u‖) : 1 / 2 ≤ ‖localPlaneBlend u‖ := by
  have hden : 0 < u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 + 4 := by positivity
  have hsq16 : 16 ≤ u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 := by
    rw [← norm_sq_r4]
    nlinarith [norm_nonneg u]
  have hp0 : (s4ProjPlane (stereo4Inv u).1) 0 ≤ -3 / 5 := by
    change (4 - (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2)) /
      (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 + 4) ≤ -3 / 5
    rw [div_le_iff₀ hden]
    linarith
  have hχ0 : 0 ≤ localRadialBump u := localRadialBump.nonneg
  have hχ1 : localRadialBump u ≤ 1 := localRadialBump.le_one
  have hmix0 : (localPlaneBlend u) 0 ≤ -3 / 5 := by
    simp only [localPlaneBlend, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, vec2_zero]
    nlinarith
  have hle : |localPlaneBlend u 0| ≤ ‖localPlaneBlend u‖ := by
    simpa using (PiLp.norm_apply_le (localPlaneBlend u) (0 : Fin 2))
  linarith [neg_le_abs (localPlaneBlend u 0)]

/-- Global smooth singular map `M → Sphere2` extending `localBallMap` along the oriented
coordinate ball `ch : ClosedManifoldChart M V_M`. -/
noncomputable def closedManifoldLocalMap {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M]
    [MeasurableSpace M] [BorelSpace M] {V_M : PositiveVolumeForm (𝓡 4) M}
    (ch : ClosedManifoldChart M V_M) (m : M) : Sphere2 :=
  letI := Classical.dec (m ∈ Set.range ch.emb)
  if hm : m ∈ Set.range ch.emb then
    localBallMap (ch.diffeo.symm ⟨m, hm⟩)
  else
    southPoleStereoInv (vec2 (-1) 0)

@[simp]
theorem closedManifoldLocalMap_emb {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M]
    [MeasurableSpace M] [BorelSpace M] {V_M : PositiveVolumeForm (𝓡 4) M}
    (ch : ClosedManifoldChart M V_M) (u : EuclideanSpace ℝ (Fin 4)) :
    closedManifoldLocalMap ch (ch.emb u) = localBallMap u := by
  have hm : ch.emb u ∈ Set.range ch.emb := ⟨u, rfl⟩
  simp only [closedManifoldLocalMap, dite_eq_left hm, ch.diffeo_symm_apply]

theorem closedManifoldLocalMap_eq_const_of_notMem_closedImage {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M]
    [MeasurableSpace M] [BorelSpace M] {V_M : PositiveVolumeForm (𝓡 4) M}
    (ch : ClosedManifoldChart M V_M) {m : M}
    (hm : m ∉ ch.emb '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) (9 / 2)) :
    closedManifoldLocalMap ch m = southPoleStereoInv (vec2 (-1) 0) := by
  by_cases hrange : m ∈ Set.range ch.emb
  · let u := ch.diffeo.symm ⟨m, hrange⟩
    have hm_eq : ch.emb u = m := ch.apply_diffeo_symm hrange
    have hu_not : u ∉ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) (9 / 2) :=
      fun hu ↦ hm ⟨u, hu, hm_eq⟩
    rw [← hm_eq, closedManifoldLocalMap_emb]
    exact localBallMap_eq_const_of_notMem_closedBall hu_not
  · simp [closedManifoldLocalMap, hrange]

/-- Global $C^\infty$ smoothness of `closedManifoldLocalMap ch : M → Sphere2`. -/
-- tier: T2
theorem contMDiff_closedManifoldLocalMap {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] {V_M : PositiveVolumeForm (𝓡 4) M}
    (ch : ClosedManifoldChart M V_M) :
    ContMDiff (𝓡 4) (𝓡 2) ∞ (closedManifoldLocalMap ch) := by
  let K : Set M := ch.emb '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) (9 / 2)
  have hK_closed : IsClosed K :=
    ((isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 4)) (9 / 2)).image
      ch.isOpenEmbedding.continuous).isClosed
  intro m
  by_cases hm : m ∈ Set.range ch.emb
  · have hcomp :
        (closedManifoldLocalMap ch ∘ (Subtype.val : ch.isLocalDiffeomorph.image → M)) =
          localBallMap ∘ ⇑ch.diffeo.symm := by
      funext y
      have hy : ch.emb (ch.diffeo.symm y) = y.1 := ch.apply_diffeo_symm y.2
      change closedManifoldLocalMap ch y.1 = _
      conv_lhs => rw [← hy]
      exact closedManifoldLocalMap_emb ch (ch.diffeo.symm y)
    refine ((TauCeti.isLocalDiffeomorph_subtype_val (I := 𝓡 4) (n := ∞)
        (⟨m, hm⟩ : ch.isLocalDiffeomorph.image)).contMDiffAt_comp_iff le_rfl).mp ?_
    rw [hcomp]
    exact (contMDiff_localBallMap.comp ch.diffeo.symm.contMDiff) ⟨m, hm⟩
  · have hmK : m ∉ K := by
      rintro ⟨u, -, rfl⟩
      exact hm ⟨u, rfl⟩
    refine (contMDiffAt_const (c := southPoleStereoInv (vec2 (-1) 0))).congr_of_eventuallyEq ?_
    filter_upwards [hK_closed.isOpen_compl.mem_nhds hmK] with y hy
    exact closedManifoldLocalMap_eq_const_of_notMem_closedImage ch hy

theorem localBallMap_mem_s4BaseRegion_iff (u : EuclideanSpace ℝ (Fin 4)) :
    localBallMap u ∈ s4BaseRegion.1 ↔ stereo4Inv u ∈ s4PreimageOpen.1 := by
  change southPoleStereoInv (localPlaneBlend u) ∈
      southPoleStereoInv '' Metric.ball (0 : EuclideanPlane) (1 / 2) ↔ _
  rw [injective_southPoleStereoInv.mem_set_image, Metric.mem_ball, dist_zero_right]
  change ‖localPlaneBlend u‖ < 1 / 2 ↔
    s4Fibration (stereo4Inv u) ∈ southPoleStereoInv '' Metric.ball (0 : EuclideanPlane) (1 / 2)
  rw [show s4Fibration (stereo4Inv u) = southPoleStereoInv (s4ProjPlane (stereo4Inv u).1) from rfl,
    injective_southPoleStereoInv.mem_set_image, Metric.mem_ball, dist_zero_right]
  constructor
  · intro hlt
    have hu4 : ‖u‖ < 4 := by
      by_contra! hge
      exact absurd hlt (not_lt_of_ge (norm_localPlaneBlend_ge_half_of_four_le hge))
    have hmem : u ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) 4 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hu4.le
    have h1 : localRadialBump u = 1 := localRadialBump.one_of_mem_closedBall hmem
    have hbl : localPlaneBlend u = s4ProjPlane (stereo4Inv u).1 := by
      simp [localPlaneBlend, h1]
    rwa [← hbl]
  · intro hp
    have hu4 : ‖u‖ < 4 := norm_lt_four_of_norm_proj_lt_half hp
    have hmem : u ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) 4 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hu4.le
    have h1 : localRadialBump u = 1 := localRadialBump.one_of_mem_closedBall hmem
    have hbl : localPlaneBlend u = s4ProjPlane (stereo4Inv u).1 := by
      simp [localPlaneBlend, h1]
    rwa [hbl]

theorem s4PreimageOpen_subset_puncturedWest :
    s4PreimageOpen.1 ⊆ s4PuncturedWest.1 := by
  intro x hx hwest
  rw [hwest, mem_preimage_s4BaseRegion_iff] at hx
  have hnorm : ‖s4ProjPlane s4WestPole.1‖ = 1 := by
    have hsq : ‖s4ProjPlane s4WestPole.1‖ ^ 2 = 1 := by
      rw [norm_sq_plane]; simp [s4WestPole]
    nlinarith [norm_nonneg (s4ProjPlane s4WestPole.1)]
  linarith

/-- Open preimage `closedManifoldLocalMap ch ⁻¹' s4BaseRegion.1` in `M`. -/
noncomputable abbrev localPreimageOpen {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] {V_M : PositiveVolumeForm (𝓡 4) M}
    (ch : ClosedManifoldChart M V_M) : Opens M :=
  ⟨closedManifoldLocalMap ch ⁻¹' s4BaseRegion.1,
    s4BaseRegion.2.preimage (contMDiff_closedManifoldLocalMap ch).continuous⟩

theorem mem_localPreimageOpen_iff {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] {V_M : PositiveVolumeForm (𝓡 4) M}
    (ch : ClosedManifoldChart M V_M) (m : M) :
    m ∈ (localPreimageOpen ch).1 ↔
      ∃ hm : m ∈ Set.range ch.emb,
        stereo4Inv (ch.diffeo.symm ⟨m, hm⟩) ∈ s4PreimageOpen.1 := by
  by_cases hm : m ∈ Set.range ch.emb
  · let u := ch.diffeo.symm ⟨m, hm⟩
    have hm_eq : ch.emb u = m := ch.apply_diffeo_symm hm
    change closedManifoldLocalMap ch m ∈ s4BaseRegion.1 ↔ _
    conv_lhs => rw [← hm_eq, closedManifoldLocalMap_emb]
    rw [localBallMap_mem_s4BaseRegion_iff]
    exact ⟨fun hu ↦ ⟨hm, hu⟩, fun ⟨_, hu⟩ ↦ hu⟩
  · constructor
    · intro hmem
      have hconst : closedManifoldLocalMap ch m = southPoleStereoInv (vec2 (-1) 0) := by
        simp [closedManifoldLocalMap, hm]
      change closedManifoldLocalMap ch m ∈ s4BaseRegion.1 at hmem
      rw [hconst] at hmem
      change southPoleStereoInv (vec2 (-1) 0) ∈
        southPoleStereoInv '' Metric.ball (0 : EuclideanPlane) (1 / 2) at hmem
      rw [injective_southPoleStereoInv.mem_set_image, Metric.mem_ball, dist_zero_right] at hmem
      have hnorm : ‖vec2 (-1) 0‖ = 1 := by
        have hsq : ‖vec2 (-1) 0‖ ^ 2 = 1 := by rw [norm_sq_plane]; norm_num
        nlinarith [norm_nonneg (vec2 (-1) 0)]
      linarith
    · rintro ⟨hm', _⟩
      exact absurd hm' hm

/-- Smooth diffeomorphism `localPreimageOpen ch ≃ₘ⟮𝓡 4, 𝓡 4⟯ s4PreimageOpen`. -/
noncomputable def localToS4PreimageDiffeomorph {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] {V_M : PositiveVolumeForm (𝓡 4) M}
    (ch : ClosedManifoldChart M V_M) :
    localPreimageOpen ch ≃ₘ⟮𝓡 4, 𝓡 4⟯ s4PreimageOpen where
  toFun m :=
    ⟨stereo4Inv (ch.diffeo.symm ⟨m.1, ((mem_localPreimageOpen_iff ch m.1).mp m.2).1⟩),
      ((mem_localPreimageOpen_iff ch m.1).mp m.2).2⟩
  invFun x :=
    ⟨ch.emb (stereo4Chart x.1), (mem_localPreimageOpen_iff ch _).mpr ⟨⟨stereo4Chart x.1, rfl⟩, by
      have hx_ne : x.1 ≠ s4WestPole := s4PreimageOpen_subset_puncturedWest x.2
      rw [ch.diffeo_symm_apply, stereo4Inv_chart hx_ne]
      exact x.2⟩⟩
  left_inv m := by
    apply Subtype.ext
    have hm_range := ((mem_localPreimageOpen_iff ch m.1).mp m.2).1
    dsimp only
    rw [stereo4Chart_inv]
    exact ch.apply_diffeo_symm hm_range
  right_inv x := by
    apply Subtype.ext
    dsimp only
    rw [ch.diffeo_symm_apply, stereo4Inv_chart (s4PreimageOpen_subset_puncturedWest x.2)]
  contMDiff_toFun := by
    refine (TauCeti.ContMDiff.subtypeVal_comp_iff s4PreimageOpen _).mp ?_
    have hm_incl :
        ContMDiff (𝓡 4) (𝓡 4) ∞
          (fun m : localPreimageOpen ch ↦
            (⟨m.1, ((mem_localPreimageOpen_iff ch m.1).mp m.2).1⟩ :
              ch.isLocalDiffeomorph.image)) :=
      (TauCeti.ContMDiff.subtypeVal_comp_iff ch.isLocalDiffeomorph.image _).mp
        contMDiff_subtype_val
    exact contMDiff_stereo4Inv.comp (ch.diffeo.symm.contMDiff.comp hm_incl)
  contMDiff_invFun := by
    refine (TauCeti.ContMDiff.subtypeVal_comp_iff (localPreimageOpen ch) _).mp ?_
    have hx_incl :
        ContMDiff (𝓡 4) (𝓡 4) ∞
          (fun x : s4PreimageOpen ↦
            (⟨x.1, s4PreimageOpen_subset_puncturedWest x.2⟩ : s4PuncturedWest)) :=
      (TauCeti.ContMDiff.subtypeVal_comp_iff s4PuncturedWest _).mp contMDiff_subtype_val
    exact ch.isLocalDiffeomorph.contMDiff.comp (stereo4Diffeomorph.symm.contMDiff.comp hx_incl)

/-- Smooth trivialization `localPreimageOpen ch ≃ₘ s4BaseRegion × Sphere2`. -/
noncomputable def closedManifoldTrivialization {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] {V_M : PositiveVolumeForm (𝓡 4) M}
    (ch : ClosedManifoldChart M V_M) :
    localPreimageOpen ch ≃ₘ⟮𝓡 4, (𝓡 2).prod (𝓡 2)⟯ (s4BaseRegion × Sphere2) :=
  (localToS4PreimageDiffeomorph ch).trans s4Trivialization

theorem closedManifoldTrivialization_fst {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] {V_M : PositiveVolumeForm (𝓡 4) M}
    (ch : ClosedManifoldChart M V_M) (p : localPreimageOpen ch) :
    (closedManifoldTrivialization ch p).1 = ⟨closedManifoldLocalMap ch p.1, p.2⟩ := by
  change (s4Trivialization (localToS4PreimageDiffeomorph ch p)).1 = _
  rw [s4Trivialization_fst]
  apply Subtype.ext
  have hp := (mem_localPreimageOpen_iff ch p.1).mp p.2
  let u := ch.diffeo.symm ⟨p.1, hp.1⟩
  have hp_eq : ch.emb u = p.1 := ch.apply_diffeo_symm hp.1
  have hu4 : ‖u‖ < 4 := by
    have hs4 : ‖s4ProjPlane (stereo4Inv u).1‖ < 1 / 2 :=
      (mem_preimage_s4BaseRegion_iff (stereo4Inv u)).mp hp.2
    exact norm_lt_four_of_norm_proj_lt_half hs4
  change s4Fibration (stereo4Inv u) = closedManifoldLocalMap ch p.1
  conv_rhs => rw [← hp_eq, closedManifoldLocalMap_emb]
  exact (localBallMap_eq_s4Fibration_of_norm_le_four hu4.le).symm

/-- Every point in `localPreimageOpen ch` is regular (`mfderiv` of `closedManifoldLocalMap ch` is
surjective), deduced directly by factoring `Subtype.val ∘ Prod.fst ∘ closedManifoldTrivialization`.
-/
-- tier: T2
theorem regular_on_closedManifoldLocalMap {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] {V_M : PositiveVolumeForm (𝓡 4) M}
    (ch : ClosedManifoldChart M V_M) :
    ∀ p ∈ closedManifoldLocalMap ch ⁻¹' s4BaseRegion.1,
      Function.Surjective (mfderiv (𝓡 4) (𝓡 2) (closedManifoldLocalMap ch) p) := by
  intro p hp
  let p' : localPreimageOpen ch := ⟨p, hp⟩
  have hcomp_eq :
      closedManifoldLocalMap ch ∘ (Subtype.val : localPreimageOpen ch → M) =
        (Subtype.val : s4BaseRegion → Sphere2) ∘
          (Prod.fst ∘ ⇑(closedManifoldTrivialization ch)) := by
    funext q
    exact congrArg Subtype.val (closedManifoldTrivialization_fst ch q).symm
  have hsub_in : MDifferentiableAt (𝓡 4) (𝓡 4) (Subtype.val : localPreimageOpen ch → M) p' :=
    (TauCeti.isLocalDiffeomorph_subtype_val (I := 𝓡 4) (n := ∞) p').contMDiffAt.mdifferentiableAt
      (by simp)
  have hf_at : MDifferentiableAt (𝓡 4) (𝓡 2) (closedManifoldLocalMap ch) p :=
    ((contMDiff_closedManifoldLocalMap ch) p).mdifferentiableAt (by simp)
  have htriv_at : MDifferentiableAt (𝓡 4) ((𝓡 2).prod (𝓡 2))
      (⇑(closedManifoldTrivialization ch)) p' :=
    ((closedManifoldTrivialization ch).contMDiff p').mdifferentiableAt (by simp)
  have hfst_at : MDifferentiableAt ((𝓡 2).prod (𝓡 2)) (𝓡 2)
      (Prod.fst : s4BaseRegion × Sphere2 → s4BaseRegion) (closedManifoldTrivialization ch p') :=
    ((contMDiff_fst (n := ∞)) (closedManifoldTrivialization ch p')).mdifferentiableAt (by simp)
  have hsub_out : MDifferentiableAt (𝓡 2) (𝓡 2) (Subtype.val : s4BaseRegion → Sphere2)
      (closedManifoldTrivialization ch p').1 :=
    (TauCeti.isLocalDiffeomorph_subtype_val (I := 𝓡 2) (n := ∞)
      (closedManifoldTrivialization ch p').1).contMDiffAt.mdifferentiableAt (by simp)
  have hlhs_comp :
      mfderiv (𝓡 4) (𝓡 2)
          (closedManifoldLocalMap ch ∘ (Subtype.val : localPreimageOpen ch → M)) p' =
        (mfderiv (𝓡 4) (𝓡 2) (closedManifoldLocalMap ch) p).comp
          (mfderiv (𝓡 4) (𝓡 4) (Subtype.val : localPreimageOpen ch → M) p') :=
    mfderiv_comp p' hf_at hsub_in
  have hrhs_comp :
      mfderiv (𝓡 4) (𝓡 2)
          ((Subtype.val : s4BaseRegion → Sphere2) ∘
            (Prod.fst ∘ ⇑(closedManifoldTrivialization ch))) p' =
        (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : s4BaseRegion → Sphere2)
            (closedManifoldTrivialization ch p').1).comp
          ((mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 2)
              (Prod.fst : s4BaseRegion × Sphere2 → s4BaseRegion)
              (closedManifoldTrivialization ch p')).comp
            (mfderiv (𝓡 4) ((𝓡 2).prod (𝓡 2))
              (⇑(closedManifoldTrivialization ch)) p')) := by
    rw [mfderiv_comp p' hsub_out (hfst_at.comp p' htriv_at),
      mfderiv_comp p' hfst_at htriv_at]
    rfl
  have hsurj_triv : Function.Surjective
      (mfderiv (𝓡 4) ((𝓡 2).prod (𝓡 2)) (⇑(closedManifoldTrivialization ch)) p') :=
    ((closedManifoldTrivialization ch).isLocalDiffeomorph p').isInvertible_mfderiv (by simp)
      |>.surjective
  have hsurj_fst : Function.Surjective
      (mfderiv ((𝓡 2).prod (𝓡 2)) (𝓡 2)
        (Prod.fst : s4BaseRegion × Sphere2 → s4BaseRegion)
        (closedManifoldTrivialization ch p')) := by
    intro v
    rw [mfderiv_fst]
    exact ⟨(v, 0), rfl⟩
  have hsurj_sub_out : Function.Surjective
      (mfderiv (𝓡 2) (𝓡 2) (Subtype.val : s4BaseRegion → Sphere2)
        (closedManifoldTrivialization ch p').1) :=
    (TauCeti.isLocalDiffeomorph_subtype_val (I := 𝓡 2) (n := ∞)
      (closedManifoldTrivialization ch p').1).isInvertible_mfderiv (by simp) |>.surjective
  have hsurj_rhs : Function.Surjective
      (mfderiv (𝓡 4) (𝓡 2)
        ((Subtype.val : s4BaseRegion → Sphere2) ∘
          (Prod.fst ∘ ⇑(closedManifoldTrivialization ch))) p') := by
    rw [hrhs_comp]
    exact hsurj_sub_out.comp (hsurj_fst.comp hsurj_triv)
  rw [← hcomp_eq, hlhs_comp] at hsurj_rhs
  exact Function.Surjective.of_comp hsurj_rhs

/-- Explicit global `RegularDiskFibration (𝓡 4) M (𝓡 2) Sphere2 Sphere2` over `s4BaseRegion` on any
nonempty Hausdorff smooth 4-manifold `(M, V_M)`. -/
noncomputable def closedManifoldRegularDiskFibration {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] {V_M : PositiveVolumeForm (𝓡 4) M}
    (ch : ClosedManifoldChart M V_M) :
    RegularDiskFibration (𝓡 4) M (𝓡 2) Sphere2 Sphere2 where
  toFun := closedManifoldLocalMap ch
  contMDiff_toFun := contMDiff_closedManifoldLocalMap ch
  baseRegion := s4BaseRegion
  baseRegion_nonempty := s4BaseRegion_nonempty
  regular_on_preimage := regular_on_closedManifoldLocalMap ch
  baseDiskRadius := s4BaseDiskRadius
  baseDiskRadius_pos := s4BaseDiskRadius_pos
  baseDisk := s4BaseDiskDiffeomorph
  trivialization := closedManifoldTrivialization ch
  trivialization_fst := closedManifoldTrivialization_fst ch

private theorem mpullback_congr_fun_local
    {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [IsManifold I₁ 1 M₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    [IsManifold I₂ 1 M₂] {f g : M₁ → M₂}
    (hf : ContMDiff I₁ I₂ ∞ f) (hg : ContMDiff I₁ I₂ ∞ g) (hfg : f = g)
    {k : ℕ} (α : TauCeti.SmoothForm I₂ M₂ ℝ k) :
    TauCeti.SmoothForm.mpullback f hf α = TauCeti.SmoothForm.mpullback g hg α := by
  subst hfg
  rfl

private theorem localToS4PreimageDiffeomorph_mpullback_s4VolumeForm
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [T2Space M]
    {V_M : PositiveVolumeForm (𝓡 4) M} (ch : ClosedManifoldChart M V_M)
    (p : localPreimageOpen ch) :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      (TauCeti.SmoothForm.mpullback (localToS4PreimageDiffeomorph ch)
          (localToS4PreimageDiffeomorph ch).contMDiff
          (TauCeti.SmoothForm.mpullback (Subtype.val : s4PreimageOpen → Sphere4)
            contMDiff_subtype_val S4VolumeForm)).1 p =
        c₁ • (TauCeti.SmoothForm.mpullback (Subtype.val : localPreimageOpen ch → M)
          contMDiff_subtype_val V_M.Ω).1 p := by
  let Φ := localToS4PreimageDiffeomorph ch
  let uOfM : localPreimageOpen ch → EuclideanSpace ℝ (Fin 4) := fun q ↦
    ch.diffeo.symm ⟨q.1, ((mem_localPreimageOpen_iff ch q.1).mp q.2).1⟩
  have huOfM_smooth : ContMDiff (𝓡 4) (𝓡 4) ∞ uOfM := by
    have hincl : ContMDiff (𝓡 4) (𝓡 4) ∞
        (fun q : localPreimageOpen ch ↦
          (⟨q.1, ((mem_localPreimageOpen_iff ch q.1).mp q.2).1⟩ : ch.isLocalDiffeomorph.image)) :=
      (TauCeti.ContMDiff.subtypeVal_comp_iff ch.isLocalDiffeomorph.image _).mp
        contMDiff_subtype_val
    exact ch.diffeo.symm.contMDiff.comp hincl
  obtain ⟨c, hc_pos, hc_eq⟩ := ch.pos_cooriented (uOfM p)
  have hcomp_M : ch.emb ∘ uOfM = (Subtype.val : localPreimageOpen ch → M) := by
    funext q
    exact ch.apply_diffeo_symm ((mem_localPreimageOpen_iff ch q.1).mp q.2).1
  have hcomp_S4 : stereo4Inv ∘ uOfM = (Subtype.val : s4PreimageOpen → Sphere4) ∘ Φ := by
    funext q
    rfl
  have hM_pull :
      TauCeti.SmoothForm.mpullback (Subtype.val : localPreimageOpen ch → M)
          contMDiff_subtype_val V_M.Ω =
        TauCeti.SmoothForm.mpullback uOfM huOfM_smooth
          (TauCeti.SmoothForm.mpullback ch.emb ch.isLocalDiffeomorph.contMDiff V_M.Ω) := by
    rw [TauCeti.SmoothForm.mpullback_mpullback uOfM ch.emb huOfM_smooth
      ch.isLocalDiffeomorph.contMDiff V_M.Ω]
    exact mpullback_congr_fun_local contMDiff_subtype_val
      (ch.isLocalDiffeomorph.contMDiff.comp huOfM_smooth) hcomp_M.symm V_M.Ω
  have hS4_pull :
      TauCeti.SmoothForm.mpullback Φ Φ.contMDiff
          (TauCeti.SmoothForm.mpullback (Subtype.val : s4PreimageOpen → Sphere4)
            contMDiff_subtype_val S4VolumeForm) =
        TauCeti.SmoothForm.mpullback uOfM huOfM_smooth stereo4PullbackVolume := by
    rw [stereo4PullbackVolume,
      TauCeti.SmoothForm.mpullback_mpullback Φ (Subtype.val : s4PreimageOpen → Sphere4)
        Φ.contMDiff contMDiff_subtype_val S4VolumeForm,
      TauCeti.SmoothForm.mpullback_mpullback uOfM stereo4Inv huOfM_smooth
        contMDiff_stereo4Inv S4VolumeForm]
    exact mpullback_congr_fun_local (contMDiff_subtype_val.comp Φ.contMDiff)
      (contMDiff_stereo4Inv.comp huOfM_smooth) hcomp_S4.symm S4VolumeForm
  have hprop :
      (TauCeti.SmoothForm.mpullback (Subtype.val : localPreimageOpen ch → M)
          contMDiff_subtype_val V_M.Ω).1 p =
        c • (TauCeti.SmoothForm.mpullback Φ Φ.contMDiff
          (TauCeti.SmoothForm.mpullback (Subtype.val : s4PreimageOpen → Sphere4)
            contMDiff_subtype_val S4VolumeForm)).1 p := by
    rw [hM_pull, hS4_pull]
    ext v
    rw [TauCeti.SmoothForm.mpullback_apply uOfM huOfM_smooth
        (TauCeti.SmoothForm.mpullback ch.emb ch.isLocalDiffeomorph.contMDiff V_M.Ω) p v,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul,
      TauCeti.SmoothForm.mpullback_apply uOfM huOfM_smooth stereo4PullbackVolume p v]
    have hpt := DFunLike.congr_fun hc_eq (fun i ↦ mfderiv (𝓡 4) (𝓡 4) uOfM p (v i))
    simpa only [ContinuousAlternatingMap.smul_apply, smul_eq_mul] using hpt
  refine ⟨c⁻¹, inv_pos.mpr hc_pos, ?_⟩
  rw [hprop, smul_smul, inv_mul_cancel₀ hc_pos.ne', one_smul]

private theorem exists_pos_smul_mpullback_closedManifoldTrivialization
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [T2Space M]
    {V_M : PositiveVolumeForm (𝓡 4) M} (ch : ClosedManifoldChart M V_M) {k : ℕ}
    (γ : TauCeti.SmoothForm ((𝓡 2).prod (𝓡 2)) (s4BaseRegion × Sphere2) ℝ k)
    (β : TauCeti.SmoothForm (𝓡 4) s4PreimageOpen ℝ k)
    (α : TauCeti.SmoothForm (𝓡 4) (localPreimageOpen ch) ℝ k)
    (p : localPreimageOpen ch)
    (h₂ : ∃ c₂ : ℝ, 0 < c₂ ∧
      (TauCeti.SmoothForm.mpullback s4Trivialization s4Trivialization.contMDiff γ).1
        (localToS4PreimageDiffeomorph ch p) = c₂ • β.1 (localToS4PreimageDiffeomorph ch p))
    (h₁ : ∃ c₁ : ℝ, 0 < c₁ ∧
      (TauCeti.SmoothForm.mpullback (localToS4PreimageDiffeomorph ch)
        (localToS4PreimageDiffeomorph ch).contMDiff β).1 p = c₁ • α.1 p) :
    ∃ c : ℝ, 0 < c ∧
      (TauCeti.SmoothForm.mpullback (closedManifoldTrivialization ch)
        (closedManifoldTrivialization ch).contMDiff γ).1 p = c • α.1 p := by
  let Φ := localToS4PreimageDiffeomorph ch
  obtain ⟨c₂, hc₂_pos, hc₂_eq⟩ := h₂
  obtain ⟨c₁, hc₁_pos, hc₁_eq⟩ := h₁
  have hcomp :
      TauCeti.SmoothForm.mpullback (closedManifoldTrivialization ch)
          (closedManifoldTrivialization ch).contMDiff γ =
        TauCeti.SmoothForm.mpullback Φ Φ.contMDiff
          (TauCeti.SmoothForm.mpullback s4Trivialization s4Trivialization.contMDiff γ) := by
    rw [TauCeti.SmoothForm.mpullback_mpullback Φ s4Trivialization
      Φ.contMDiff s4Trivialization.contMDiff γ]
    exact mpullback_congr_fun_local (closedManifoldTrivialization ch).contMDiff
      (s4Trivialization.contMDiff.comp Φ.contMDiff)
      (Diffeomorph.coe_trans Φ s4Trivialization) γ
  refine ⟨c₂ * c₁, mul_pos hc₂_pos hc₁_pos, ?_⟩
  rw [hcomp]
  apply ContinuousAlternatingMap.ext
  intro v
  rw [TauCeti.SmoothForm.mpullback_apply Φ Φ.contMDiff _ p v,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  have h2 := DFunLike.congr_fun hc₂_eq (fun i ↦ mfderiv (𝓡 4) (𝓡 4) ⇑Φ p (v i))
  rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h2
  have h1 := DFunLike.congr_fun hc₁_eq v
  rw [TauCeti.SmoothForm.mpullback_apply Φ Φ.contMDiff β p v,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h1
  rw [h2, h1, mul_assoc]

/-- Strict positive co-orientation of `closedManifoldTrivialization ch` with `S2VolumeForm` and
`V_M.Ω`. -/
-- tier: T2
theorem closedManifoldTrivialization_pos_cooriented {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] {V_M : PositiveVolumeForm (𝓡 4) M}
    (ch : ClosedManifoldChart M V_M) (p : localPreimageOpen ch) :
    ∃ c : ℝ, 0 < c ∧
      (TauCeti.SmoothForm.mpullback (closedManifoldTrivialization ch)
          (closedManifoldTrivialization ch).contMDiff
          (TauCeti.SmoothForm.wedge
            (TauCeti.SmoothForm.mpullback Prod.snd contMDiff_snd S2VolumeForm)
            (TauCeti.SmoothForm.mpullback (Subtype.val ∘ Prod.fst)
              (contMDiff_subtype_val.comp contMDiff_fst) S2VolumeForm))).1 p =
        c • (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val V_M.Ω).1 p :=
  exists_pos_smul_mpullback_closedManifoldTrivialization ch _ _ _ p
    (s4Trivialization_pos_cooriented (localToS4PreimageDiffeomorph ch p))
    (localToS4PreimageDiffeomorph_mpullback_s4VolumeForm ch p)

/-- **Track B Unconditional Regular-Disk Fibration Constructor (`L-R3`, `SC-R1`)**:
Every nonempty Hausdorff smooth 4-manifold `M` equipped with a `PositiveVolumeForm` `V_M`
admits a positively co-oriented `RegularDiskFibration M → Sphere2` with regular fiber `Sphere2`.
(Marked `@[instance_reducible]`, not global `instance`, to avoid collision with `Sphere4`.) -/
@[instance_reducible]
noncomputable def AdmitsRegularDiskFibration.ofPositiveVolumeForm
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] [T2Space M]
    (V_M : PositiveVolumeForm (𝓡 4) M) :
    AdmitsRegularDiskFibration M :=
  let ch := closedManifoldChart M V_M
  { ambientVolume := V_M
    Fiber := Sphere2
    instTopologicalSpaceFiber := inferInstance
    instChartedSpaceFiber := inferInstance
    instIsManifoldFiber := inferInstance
    instT2SpaceFiber := inferInstance
    instCompactSpaceFiber := inferInstance
    instNonemptyFiber := ⟨s2NorthPole⟩
    instMeasurableSpaceFiber := inferInstance
    instBorelSpaceFiber := inferInstance
    fibration := closedManifoldRegularDiskFibration ch
    fiberVolume := S2PositiveVolumeForm
    trivialization_pos_cooriented := closedManifoldTrivialization_pos_cooriented ch }

/-! ## 4. Track B Separation: Nonempty Critical Interior & `¬ IsGenericallyRankTwo` (`SC-R2`) -/

/-- On any Hausdorff smooth 4-manifold `(M, V_M)` (in particular any compact nonempty Hausdorff
smooth 4-manifold), `criticalPoints` of `(closedManifoldRegularDiskFibration ch).toFun` has
**nonempty interior** in `M` (`closedManifoldLocalMap ch` is constant on the nonempty open set
`ch.emb '' {u : ℝ⁴ | 5 < ‖u‖}`). -/
-- tier: T2
theorem nonempty_interior_criticalPoints_closedManifoldRegularDiskFibration
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [T2Space M]
    {V_M : PositiveVolumeForm (𝓡 4) M} (ch : ClosedManifoldChart M V_M) :
    (interior
      (criticalPoints (𝓡 4) (𝓡 2) (closedManifoldRegularDiskFibration ch).toFun)).Nonempty := by
  let W_ext : Set (EuclideanSpace ℝ (Fin 4)) := {u | 5 < ‖u‖}
  have hW_open : IsOpen W_ext := isOpen_lt continuous_const continuous_norm
  let u₀ : EuclideanSpace ℝ (Fin 4) := vec4 6 0 0 0
  have hu₀_mem : u₀ ∈ W_ext := by
    change 5 < ‖u₀‖
    have hsq : ‖u₀‖ ^ 2 = 36 := by
      rw [norm_sq_r4]
      simp [u₀]
      norm_num
    nlinarith [norm_nonneg u₀]
  let U_ext : Set M := ch.emb '' W_ext
  have hU_open : IsOpen U_ext := ch.isOpenEmbedding.isOpenMap W_ext hW_open
  let c₀ : Sphere2 := southPoleStereoInv (vec2 (-1) 0)
  have hconst : ∀ y ∈ U_ext, closedManifoldLocalMap ch y = c₀ := by
    rintro _ ⟨u, hu, rfl⟩
    rw [closedManifoldLocalMap_emb]
    refine localBallMap_eq_const_of_notMem_closedBall fun hcb ↦ ?_
    have hle : ‖u‖ ≤ 9 / 2 := by simpa [Metric.mem_closedBall, dist_zero_right] using hcb
    have hgt : 5 < ‖u‖ := hu
    linarith
  have hU_sub :
      U_ext ⊆ criticalPoints (𝓡 4) (𝓡 2) (closedManifoldRegularDiskFibration ch).toFun := by
    intro x hx
    rw [mem_criticalPoints_iff]
    intro hsurj
    have hev : (closedManifoldRegularDiskFibration ch).toFun =ᶠ[𝓝 x] fun _ : M ↦ c₀ :=
      Filter.eventuallyEq_of_mem (hU_open.mem_nhds hx) hconst
    have hzero : mfderiv (𝓡 4) (𝓡 2) (closedManifoldRegularDiskFibration ch).toFun x = 0 := by
      rw [hev.mfderiv_eq, mfderiv_const, ContinuousLinearMap.comp_zero]
    rw [hzero] at hsurj
    obtain ⟨v, hv⟩ :=
      hsurj (vec2 1 0 : TangentSpace (𝓡 2) ((closedManifoldRegularDiskFibration ch).toFun x))
    have h1 : (0 : EuclideanPlane) 0 = (vec2 1 0 : EuclideanPlane) 0 :=
      congrArg (fun u : EuclideanPlane ↦ u 0) hv
    norm_num at h1
  exact ⟨ch.emb u₀, interior_maximal hU_sub hU_open ⟨u₀, hu₀_mem, rfl⟩⟩

/-- The regular locus of `closedManifoldRegularDiskFibration ch` is **not** dense in `M`. -/
-- tier: T1
theorem not_dense_regularPoints_closedManifoldRegularDiskFibration
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [T2Space M]
    {V_M : PositiveVolumeForm (𝓡 4) M} (ch : ClosedManifoldChart M V_M) :
    ¬ Dense {x : M | x ∉ criticalPoints (𝓡 4) (𝓡 2)
        (closedManifoldRegularDiskFibration ch).toFun} := by
  intro hd
  obtain ⟨x, hx⟩ := nonempty_interior_criticalPoints_closedManifoldRegularDiskFibration ch
  obtain ⟨y, hy_int, hy_reg⟩ := hd.inter_open_nonempty _ isOpen_interior ⟨x, hx⟩
  exact hy_reg (interior_subset hy_int)

/-- **Track B Anti-Vacuity Separation Theorem (`SC-R2`, `¬ IsGenericallyRankTwo`)**:
For any positive volume 4-form `V` on `M` (including the aligned volume form on compact `M`), the
Jacobian–Poisson structure `π_f` induced by `(closedManifoldRegularDiskFibration ch).toFun`
satisfies `¬ π_f.IsGenericallyRankTwo`. -/
-- tier: T1
theorem not_isGenericallyRankTwo_closedManifoldLocal
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [T2Space M]
    {V_M : PositiveVolumeForm (𝓡 4) M} (ch : ClosedManifoldChart M V_M)
    (V : PositiveVolumeForm (𝓡 4) M) :
    ¬ (jacobianPoissonOfPositiveVolume V S2VolumeForm
        (closedManifoldRegularDiskFibration ch).toFun
        (closedManifoldRegularDiskFibration ch).contMDiff_toFun).IsGenericallyRankTwo := by
  rw [isGenericallyRankTwo_jacobianPoissonOfPositiveVolume_iff V S2VolumeForm S2VolumeForm_ne_zero]
  exact not_dense_regularPoints_closedManifoldRegularDiskFibration ch

/-- **Track B Singularity Exclusion (`SC-R1` / `SC-R2`)**:
`(closedManifoldRegularDiskFibration ch).toFun` cannot underlie **any**
`AdmitsWrinkledOrBrokenLefschetzFibration M` instance on `M`. -/
-- tier: T1
theorem not_admitsWrinkledOrBrokenLefschetzFibration_closedManifoldLocal
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [T2Space M]
    {V_M : PositiveVolumeForm (𝓡 4) M} (ch : ClosedManifoldChart M V_M)
    (A : AdmitsWrinkledOrBrokenLefschetzFibration M) :
    letI := A.instTopologicalSpaceFiber
    letI := A.instChartedSpaceFiber
    letI := A.instIsManifoldFiber
    letI := A.instT2SpaceFiber
    letI := A.instCompactSpaceFiber
    letI := A.instNonemptyFiber
    A.fibration.toFun ≠ (closedManifoldRegularDiskFibration ch).toFun := by
  let _ := A.instTopologicalSpaceFiber
  let _ := A.instChartedSpaceFiber
  let _ := A.instIsManifoldFiber
  let _ := A.instT2SpaceFiber
  let _ := A.instCompactSpaceFiber
  let _ := A.instNonemptyFiber
  intro hEq
  have hd := @AdmitsWrinkledOrBrokenLefschetzFibration.dense_regularPoints M _ _ _ _ _ A
  rw [hEq] at hd
  exact not_dense_regularPoints_closedManifoldRegularDiskFibration ch hd

end LocalBumpedFibration

end S4TuringPoisson
