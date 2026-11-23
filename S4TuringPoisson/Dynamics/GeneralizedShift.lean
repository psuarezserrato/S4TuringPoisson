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

public import Mathlib.Analysis.Real.OfDigits
public import S4TuringPoisson.Interfaces

/-!
# Generalized Shifts, Turing Machine Conjugacy, and Square Cantor Embeddings (Milestone M3.1)

This module formalizes Moore's generalized shifts on bi-infinite symbolic sequences `ℤ → A`
(Moore 1990; Cardona–Miranda–Peralta-Salas–Presas 2021, Section 4) and connects them to Mathlib's
`Turing.TM0` model and `S4TuringPoisson.Interfaces`:

1. **Moore's Generalized Shifts (`GeneralizedShift`)**:
   - Finite domain of dependence `D : Finset ℤ`, local shift `F : (D → A) → ℤ`, local block
     replacement `G : (D → A) → (D → A)`, two-domain constructor `GeneralizedShift.ofTwoDomains`
     (`D_F`, `D_G`), induced global map `GeneralizedShift.eval`, and product-topology continuity
     `GeneralizedShift.continuous_eval`.

2. **CMPP21 Proposition 4.4 — Reversible Bijective & Arbitrary `FinTM0` Conjugacy on `{-1, 0, 1}`**:
   - `ReversibleTM`: unidirectional reversible Turing machines (`stepPerm : (Q × Γ) ≃ (Q × Γ)`,
     `dirIn : Q → ShiftDir`), conjugated to `ReversibleTM.toGeneralizedShift` on
     `shiftDom3 = {-1, 0, 1}` with explicit inverse generalized shift
     `ReversibleTM.invGeneralizedShift` on `{-1, 0, 1}`, yielding `ReversibleTM.toEquiv` and
     `ReversibleTM.bijective_eval`.
   - `FinTM0.toGeneralizedShift`: conjugates any `M : FinTM0` to a generalized shift on
     `D_F = D_G = {-1, 0, 1}` over the finite alphabet `M.Γ × Option (Option M.Λ)` (adjoining a
     dedicated terminal state `none` on head-centered `Turing.Tape`), proving step-by-step orbit
     simulation and exact equivalence between `HaltsWithWindow M t k w` and hitting the nonempty
     cylinder `cylinderIcc k (M.haltWindow k w)`.

3. **Odd-Base Square Cantor Embedding `(ℤ → A) ↪ UnitDisk2` & `Computable` `2⁻ᵐ` Approximations**:
   - Base-`max (2|A| - 1, 3)` middle-Cantor coordinate `scaledCantorCoord` built on
     `Real.ofDigits`, mapping finite prefixes to pairwise disjoint nonempty open intervals inside
     `(-1/2, 1/2)`.
   - Continuous injective square Cantor embedding `cantorDiskEmbed : (ℤ → A) → UnitDisk2` mapping
     finite `[-k, k]` cylinder blocks to pairwise disjoint nonempty open rectangles
     `cantorCylinderRect` inside `UnitDisk2`, together with primitive-recursive (`Computable`)
     `2⁻ᵐ` rational `RatFrac × RatFrac` approximations for `M.encodeInit (Tape.mk₂ L R)` matching
     `TuringCompleteWitness.computable_approx`.
-/

@[expose] public section

open Filter Metric Set TopologicalSpace
open scoped Topology

namespace S4TuringPoisson

/-! ## 1. Moore's Generalized Shifts on `ℤ → A` -/

/-- Shift a bi-infinite sequence `s : ℤ → A` by `m : ℤ`, sending index `k` to `s (k + m)`. -/
def shiftSeq {A : Type*} (m : ℤ) (s : ℤ → A) : ℤ → A :=
  fun k ↦ s (k + m)

@[simp]
theorem shiftSeq_apply {A : Type*} (m : ℤ) (s : ℤ → A) (k : ℤ) :
    shiftSeq m s k = s (k + m) :=
  rfl

@[simp]
theorem shiftSeq_zero {A : Type*} (s : ℤ → A) : shiftSeq 0 s = s := by
  funext k
  simp [shiftSeq]

theorem shiftSeq_add {A : Type*} (m₁ m₂ : ℤ) (s : ℤ → A) :
    shiftSeq m₁ (shiftSeq m₂ s) = shiftSeq (m₁ + m₂) s := by
  funext k
  simp [shiftSeq, add_assoc]

/-- Restrict a bi-infinite sequence `s : ℤ → A` to a finite domain `D : Finset ℤ`. -/
def restrictDom {A : Type*} (D : Finset ℤ) (s : ℤ → A) : D → A :=
  fun i ↦ s i.1

@[simp]
theorem restrictDom_apply {A : Type*} (D : Finset ℤ) (s : ℤ → A) (i : D) :
    restrictDom D s i = s i.1 :=
  rfl

/-- Replace the entries of `s : ℤ → A` on `D : Finset ℤ` with the local block `w : D → A`,
leaving all coordinates outside `D` unchanged. -/
def replaceDom {A : Type*} (D : Finset ℤ) (w : D → A) (s : ℤ → A) : ℤ → A :=
  fun k ↦ if hk : k ∈ D then w ⟨k, hk⟩ else s k

@[simp]
theorem replaceDom_mem {A : Type*} (D : Finset ℤ) (w : D → A) (s : ℤ → A) {k : ℤ}
    (hk : k ∈ D) : replaceDom D w s k = w ⟨k, hk⟩ := by
  simp [replaceDom, hk]

@[simp]
theorem replaceDom_notMem {A : Type*} (D : Finset ℤ) (w : D → A) (s : ℤ → A) {k : ℤ}
    (hk : k ∉ D) : replaceDom D w s k = s k := by
  simp [replaceDom, hk]

@[simp]
theorem restrictDom_replaceDom {A : Type*} (D : Finset ℤ) (w : D → A) (s : ℤ → A) :
    restrictDom D (replaceDom D w s) = w := by
  funext ⟨k, hk⟩
  simp [hk]

/-- Moore's **generalized shift** (`Moore 1990`, `CMPP21` Definition 4.1) on bi-infinite sequences
`ℤ → A`, specified by a finite domain of dependence `D : Finset ℤ`, a local shift function
`F : (D → A) → ℤ`, and a local replacement rule `G : (D → A) → (D → A)`. -/
structure GeneralizedShift (A : Type*) where
  /-- Finite domain of dependence `D ⊂ ℤ`. -/
  D : Finset ℤ
  /-- Integer shift amount determined by the local block on `D`. -/
  F : (D → A) → ℤ
  /-- Local block replacement on `D`. -/
  G : (D → A) → (D → A)

namespace GeneralizedShift

/-- Evaluate a generalized shift `Φ` on `s : ℤ → A`: replace `s|_D` by `Φ.G (s|_D)` and shift the
resulting sequence by `Φ.F (s|_D)`. -/
def eval {A : Type*} (Φ : GeneralizedShift A) (s : ℤ → A) : ℤ → A :=
  let w := restrictDom Φ.D s
  shiftSeq (Φ.F w) (replaceDom Φ.D (Φ.G w) s)

theorem eval_apply {A : Type*} (Φ : GeneralizedShift A) (s : ℤ → A) (k : ℤ) :
    Φ.eval s k = replaceDom Φ.D (Φ.G (restrictDom Φ.D s)) s (k + Φ.F (restrictDom Φ.D s)) :=
  rfl

/-- Construct a `GeneralizedShift A` from separate domains of dependence `D_F, D_G : Finset ℤ`
(`CMPP21` Definition 4.1) over their union `D_F ∪ D_G`. -/
def ofTwoDomains {A : Type*} (D_F D_G : Finset ℤ) (F : (D_F → A) → ℤ)
    (G : (D_G → A) → (D_G → A)) : GeneralizedShift A where
  D := D_F ∪ D_G
  F w := F (fun i ↦ w ⟨i.1, Finset.mem_union_left D_G i.2⟩)
  G w i :=
    if hi : i.1 ∈ D_G then
      G (fun j ↦ w ⟨j.1, Finset.mem_union_right D_F j.2⟩) ⟨i.1, hi⟩
    else
      w i

@[simp]
theorem ofTwoDomains_D_self {A : Type*} (D : Finset ℤ) (F : (D → A) → ℤ)
    (G : (D → A) → (D → A)) :
    (ofTwoDomains D D F G).D = D :=
  Finset.union_idempotent (s := D)

theorem eval_ofTwoDomains {A : Type*} (D_F D_G : Finset ℤ) (F : (D_F → A) → ℤ)
    (G : (D_G → A) → (D_G → A)) (s : ℤ → A) :
    (ofTwoDomains D_F D_G F G).eval s =
      shiftSeq (F (restrictDom D_F s)) (replaceDom D_G (G (restrictDom D_G s)) s) := by
  funext k
  unfold eval ofTwoDomains shiftSeq restrictDom replaceDom
  dsimp only
  by_cases hG : (k + F fun i ↦ s i.1) ∈ D_G
  · have hU : (k + F fun i ↦ s i.1) ∈ D_F ∪ D_G := Finset.mem_union_right D_F hG
    simp [hU, hG]
  · by_cases hU : (k + F fun i ↦ s i.1) ∈ D_F ∪ D_G
    · simp [hU, hG]
    · simp [hU, hG]

/-- Every generalized shift is continuous with respect to the product topology on `ℤ → A` when `A`
carries the discrete topology. -/
theorem continuous_eval {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    (Φ : GeneralizedShift A) : Continuous Φ.eval := by
  rw [continuous_iff_continuousAt]
  intro s₀
  rw [ContinuousAt, tendsto_pi_nhds]
  intro k
  let m₀ := Φ.F (restrictDom Φ.D s₀)
  let S : Finset ℤ := insert (k + m₀) Φ.D
  have hU_open : IsOpen { s : ℤ → A | ∀ j ∈ S, s j = s₀ j } := by
    have heq : { s : ℤ → A | ∀ j ∈ S, s j = s₀ j } =
        ⋂ j ∈ (S : Set ℤ), (fun s : ℤ → A ↦ s j) ⁻¹' {s₀ j} := by
      ext s
      simp
    rw [heq]
    exact S.finite_toSet.isOpen_biInter fun j _ ↦
      (isOpen_discrete {s₀ j}).preimage (continuous_apply j)
  have hs₀ : s₀ ∈ { s : ℤ → A | ∀ j ∈ S, s j = s₀ j } := fun _ _ ↦ rfl
  have hev : (fun s ↦ Φ.eval s k) =ᶠ[𝓝 s₀] fun _ ↦ Φ.eval s₀ k := by
    filter_upwards [hU_open.mem_nhds hs₀] with s hs
    have hD : restrictDom Φ.D s = restrictDom Φ.D s₀ := by
      funext ⟨j, hj⟩
      exact hs j (Finset.mem_insert_of_mem hj)
    dsimp only [eval_apply]
    rw [hD]
    change replaceDom Φ.D (Φ.G (restrictDom Φ.D s₀)) s (k + m₀) =
      replaceDom Φ.D (Φ.G (restrictDom Φ.D s₀)) s₀ (k + m₀)
    by_cases hk : k + m₀ ∈ Φ.D
    · rw [replaceDom_mem _ _ _ hk, replaceDom_mem _ _ _ hk]
    · rw [replaceDom_notMem _ _ _ hk, replaceDom_notMem _ _ _ hk]
      exact hs (k + m₀) (Finset.mem_insert_self _ _)
  exact tendsto_const_nhds.congr' hev.symm

end GeneralizedShift

/-! ## 2. Radius-1 Domain `{-1, 0, 1}` & Bijective Reversible TM Conjugacy (`CMPP21` Prop. 4.4) -/

/-- Canonical 3-cell domain of dependence `{-1, 0, 1} : Finset ℤ` of `CMPP21` Proposition 4.4. -/
def shiftDom3 : Finset ℤ := {-1, 0, 1}

theorem mem_shiftDom3_iff (k : ℤ) : k ∈ shiftDom3 ↔ k = -1 ∨ k = 0 ∨ k = 1 := by
  simp [shiftDom3]

theorem notMem_shiftDom3_iff (k : ℤ) : k ∉ shiftDom3 ↔ k ≠ -1 ∧ k ≠ 0 ∧ k ≠ 1 := by
  simp [shiftDom3, not_or]

/-- Element `-1` in `shiftDom3`. -/
def dom3NegOne : shiftDom3 := ⟨-1, by simp [shiftDom3]⟩

/-- Element `0` in `shiftDom3`. -/
def dom3Zero : shiftDom3 := ⟨0, by simp [shiftDom3]⟩

/-- Element `1` in `shiftDom3`. -/
def dom3One : shiftDom3 := ⟨1, by simp [shiftDom3]⟩

@[simp] theorem dom3NegOne_coe : (dom3NegOne : ℤ) = -1 := rfl
@[simp] theorem dom3Zero_coe : (dom3Zero : ℤ) = 0 := rfl
@[simp] theorem dom3One_coe : (dom3One : ℤ) = 1 := rfl

/-- Construct a local block `shiftDom3 → A` from its values at `-1`, `0`, and `1`. -/
def mkDom3 {A : Type*} (aNeg aZero aPos : A) : shiftDom3 → A :=
  fun i ↦ if i.1 = -1 then aNeg else if i.1 = 0 then aZero else aPos

@[simp]
theorem mkDom3_negOne {A : Type*} (aNeg aZero aPos : A) :
    mkDom3 aNeg aZero aPos dom3NegOne = aNeg :=
  rfl

@[simp]
theorem mkDom3_zero {A : Type*} (aNeg aZero aPos : A) :
    mkDom3 aNeg aZero aPos dom3Zero = aZero :=
  rfl

@[simp]
theorem mkDom3_one {A : Type*} (aNeg aZero aPos : A) :
    mkDom3 aNeg aZero aPos dom3One = aPos :=
  rfl

@[simp]
theorem mkDom3_eta {A : Type*} (w : shiftDom3 → A) :
    mkDom3 (w dom3NegOne) (w dom3Zero) (w dom3One) = w := by
  funext ⟨k, hk⟩
  rcases (mem_shiftDom3_iff k).mp hk with rfl | rfl | rfl <;> rfl

@[simp]
theorem replaceDom_shiftDom3_negOne {A : Type*} (aNeg aZero aPos : A) (s : ℤ → A) :
    replaceDom shiftDom3 (mkDom3 aNeg aZero aPos) s (-1) = aNeg :=
  rfl

@[simp]
theorem replaceDom_shiftDom3_zero {A : Type*} (aNeg aZero aPos : A) (s : ℤ → A) :
    replaceDom shiftDom3 (mkDom3 aNeg aZero aPos) s 0 = aZero :=
  rfl

@[simp]
theorem replaceDom_shiftDom3_one {A : Type*} (aNeg aZero aPos : A) (s : ℤ → A) :
    replaceDom shiftDom3 (mkDom3 aNeg aZero aPos) s 1 = aPos :=
  rfl

/-- Three-way head displacement (`{-1, 0, +1}`) for generalized-shift Turing simulations. -/
inductive ShiftDir
  | left
  | stay
  | right
  deriving DecidableEq, Inhabited

/-- Integer displacement `-1`, `0`, or `1` associated to a `ShiftDir`. -/
def ShiftDir.toInt : ShiftDir → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

@[simp]
theorem tape_write_head {Γ : Type*} [Inhabited Γ] (T : Turing.Tape Γ) (b : Γ) :
    (T.write b).head = b :=
  rfl

@[simp]
theorem tape_write_write {Γ : Type*} [Inhabited Γ] (T : Turing.Tape Γ) (a b : Γ) :
    (T.write a).write b = T.write b := by
  cases T
  rfl

@[simp]
theorem tape_move_left_head {Γ : Type*} [Inhabited Γ] (T : Turing.Tape Γ) :
    (T.move Turing.Dir.left).head = T.nth (-1) :=
  Turing.Tape.move_left_nth T 0

@[simp]
theorem tape_move_right_head {Γ : Type*} [Inhabited Γ] (T : Turing.Tape Γ) :
    (T.move Turing.Dir.right).head = T.nth 1 :=
  Turing.Tape.move_right_nth T 0

/-- Unidirectional **reversible Turing machine** (`CMPP21` Definition 4.2 & Lemma 4.3):
each state-symbol pair `(q, a) : Q × Γ` transitions bijectively via `stepPerm` to `(q', b)`, and
every target state `q'` has a unique incoming shift direction `dirIn q' ∈ {left, stay, right}`. -/
structure ReversibleTM where
  /-- Tape symbol alphabet (`default` is blank). -/
  Γ : Type*
  /-- Machine state space. -/
  Q : Type*
  [instInhabitedΓ : Inhabited Γ]
  /-- Bijective state-symbol transition `(q, a) ↦ (q', b)`. -/
  stepPerm : (Q × Γ) ≃ (Q × Γ)
  /-- Unique incoming head-move direction for each target state `q'`. -/
  dirIn : Q → ShiftDir

attribute [instance] ReversibleTM.instInhabitedΓ

namespace ReversibleTM

/-- Instantaneous configuration of a `ReversibleTM` (`q : Q` and head-centered `Tape : Tape Γ`). -/
structure Cfg (R : ReversibleTM) where
  /-- Internal state. -/
  q : R.Q
  /-- Head-centered bi-infinite tape. -/
  Tape : Turing.Tape R.Γ

/-- Deterministic reversible single step of `R`: replace `(q, T.head)` with `(q', b) = stepPerm`,
write `b` at the head, and move the tape according to `dirIn q'`. -/
def step (R : ReversibleTM) (c : R.Cfg) : R.Cfg :=
  let qb := R.stepPerm (c.q, c.Tape.head)
  let T' := c.Tape.write qb.2
  match R.dirIn qb.1 with
  | .left => ⟨qb.1, T'.move Turing.Dir.left⟩
  | .stay => ⟨qb.1, T'⟩
  | .right => ⟨qb.1, T'.move Turing.Dir.right⟩

/-- Inverse single step of `R` on configurations. -/
def invStep (R : ReversibleTM) (c : R.Cfg) : R.Cfg :=
  let T_prev :=
    match R.dirIn c.q with
    | .left => c.Tape.move Turing.Dir.right
    | .stay => c.Tape
    | .right => c.Tape.move Turing.Dir.left
  let qa := R.stepPerm.symm (c.q, T_prev.head)
  ⟨qa.1, T_prev.write qa.2⟩

@[simp]
theorem invStep_step (R : ReversibleTM) (c : R.Cfg) : R.invStep (R.step c) = c := by
  rcases c with ⟨q, ⟨hd, L, Rt⟩⟩
  dsimp only [step, invStep]
  generalize hqb : R.stepPerm (q, hd) = qb
  rcases qb with ⟨q', b⟩
  have hsymm : R.stepPerm.symm (q', b) = (q, hd) := R.stepPerm.symm_apply_eq.mpr hqb.symm
  rcases hdir : R.dirIn q'
  · simp [hdir, Turing.Tape.write, hsymm]
  · simp [hdir, Turing.Tape.write, hsymm]
  · simp [hdir, Turing.Tape.write, hsymm]

@[simp]
theorem step_invStep (R : ReversibleTM) (c : R.Cfg) : R.step (R.invStep c) = c := by
  rcases c with ⟨q', T⟩
  dsimp only [step, invStep]
  rcases hdir : R.dirIn q'
  · generalize hqa : R.stepPerm.symm (q', (T.move Turing.Dir.right).head) = qa
    rcases qa with ⟨q, a⟩
    have hfwd : R.stepPerm (q, a) = (q', (T.move Turing.Dir.right).head) :=
      R.stepPerm.eq_symm_apply.mp hqa.symm
    have hself : (T.move Turing.Dir.right).write (T.nth 1) = T.move Turing.Dir.right := by
      rw [← tape_move_right_head T]
      exact Turing.Tape.write_self _
    simp [hfwd, hdir, hself]
  · generalize hqa : R.stepPerm.symm (q', T.head) = qa
    rcases qa with ⟨q, a⟩
    have hfwd : R.stepPerm (q, a) = (q', T.head) :=
      R.stepPerm.eq_symm_apply.mp hqa.symm
    simp [hfwd, hdir]
  · generalize hqa : R.stepPerm.symm (q', (T.move Turing.Dir.left).head) = qa
    rcases qa with ⟨q, a⟩
    have hfwd : R.stepPerm (q, a) = (q', (T.move Turing.Dir.left).head) :=
      R.stepPerm.eq_symm_apply.mp hqa.symm
    have hself : (T.move Turing.Dir.left).write (T.nth (-1)) = T.move Turing.Dir.left := by
      rw [← tape_move_left_head T]
      exact Turing.Tape.write_self _
    simp [hfwd, hdir, hself]

/-- `R.step` packaged as a bijection `R.Cfg ≃ R.Cfg`. -/
def stepEquiv (R : ReversibleTM) : R.Cfg ≃ R.Cfg where
  toFun := R.step
  invFun := R.invStep
  left_inv := R.invStep_step
  right_inv := R.step_invStep

/-- Shift alphabet `R.Γ × Option R.Q` encoding tape symbol and optional head state at each cell. -/
abbrev ShiftAlphabet (R : ReversibleTM) : Type _ :=
  R.Γ × Option R.Q

/-- Encode a reversible TM configuration `c` into `ℤ → R.ShiftAlphabet`, placing `some c.q` at
cell `0` (head position) and `none` at all nonzero cells. -/
def encodeCfg (R : ReversibleTM) (c : R.Cfg) : ℤ → R.ShiftAlphabet :=
  fun i ↦ (c.Tape.nth i, if i = 0 then some c.q else none)

/-- Forward generalized shift on `D = {-1, 0, 1}` realizing `R` (`CMPP21` Proposition 4.4).
Swapping the optional state marker between cell `0` and the target cell `±1` makes the global shift
bijective on *all* sequences in `ℤ → R.ShiftAlphabet` while matching `R.step` on valid 1-head
configurations. -/
def toGeneralizedShift (R : ReversibleTM) : GeneralizedShift R.ShiftAlphabet where
  D := shiftDom3
  F w :=
    match (w dom3Zero).2 with
    | none => 0
    | some q => (R.dirIn (R.stepPerm (q, (w dom3Zero).1)).1).toInt
  G w :=
    match (w dom3Zero).2 with
    | none => w
    | some q =>
      let qb := R.stepPerm (q, (w dom3Zero).1)
      match R.dirIn qb.1 with
      | .left =>
        mkDom3 ((w dom3NegOne).1, some qb.1) (qb.2, (w dom3NegOne).2) (w dom3One)
      | .stay =>
        mkDom3 (w dom3NegOne) (qb.2, some qb.1) (w dom3One)
      | .right =>
        mkDom3 (w dom3NegOne) (qb.2, (w dom3One).2) ((w dom3One).1, some qb.1)

@[simp]
theorem toGeneralizedShift_D (R : ReversibleTM) : R.toGeneralizedShift.D = shiftDom3 :=
  rfl

/-- Explicit inverse generalized shift on `D = {-1, 0, 1}` for `R.toGeneralizedShift`. -/
def invGeneralizedShift (R : ReversibleTM) : GeneralizedShift R.ShiftAlphabet where
  D := shiftDom3
  F u :=
    match (u dom3Zero).2 with
    | none => 0
    | some q' => -((R.dirIn q').toInt)
  G u :=
    match (u dom3Zero).2 with
    | none => u
    | some q' =>
      match R.dirIn q' with
      | .left =>
        let qa := R.stepPerm.symm (q', (u dom3One).1)
        mkDom3 (u dom3NegOne) ((u dom3Zero).1, (u dom3One).2) (qa.2, some qa.1)
      | .stay =>
        let qa := R.stepPerm.symm (q', (u dom3Zero).1)
        mkDom3 (u dom3NegOne) (qa.2, some qa.1) (u dom3One)
      | .right =>
        let qa := R.stepPerm.symm (q', (u dom3NegOne).1)
        mkDom3 (qa.2, some qa.1) ((u dom3Zero).1, (u dom3NegOne).2) (u dom3One)

@[simp]
theorem invGeneralizedShift_D (R : ReversibleTM) : R.invGeneralizedShift.D = shiftDom3 :=
  rfl

/-- `R.invGeneralizedShift.eval` is a left inverse to `R.toGeneralizedShift.eval` on all of
`ℤ → R.ShiftAlphabet`. -/
theorem inv_eval_to_eval (R : ReversibleTM) (s : ℤ → R.ShiftAlphabet) :
    R.invGeneralizedShift.eval (R.toGeneralizedShift.eval s) = s := by
  funext k
  let y := R.toGeneralizedShift.eval s
  change R.invGeneralizedShift.eval y k = s k
  rcases hs0 : s 0 with ⟨a₀, _ | q⟩
  · have hy : y = s := by
      funext j
      simp only [y, GeneralizedShift.eval_apply, toGeneralizedShift, restrictDom_apply,
        dom3Zero_coe, hs0, add_zero]
      by_cases hj : j ∈ shiftDom3 <;> simp [hj]
    rw [hy]
    simp only [GeneralizedShift.eval_apply, invGeneralizedShift, restrictDom_apply, dom3Zero_coe,
      hs0, add_zero]
    by_cases hk : k ∈ shiftDom3 <;> simp [hk]
  · generalize hqb : R.stepPerm (q, a₀) = qb
    rcases qb with ⟨q', b⟩
    have hsymm : R.stepPerm.symm (q', b) = (q, a₀) := R.stepPerm.symm_apply_eq.mpr hqb.symm
    rcases hdir : R.dirIn q'
    · have hy0 : y 0 = ((s (-1)).1, some q') := by
        simp [y, GeneralizedShift.eval_apply, toGeneralizedShift, hs0, hqb, hdir, ShiftDir.toInt]
      have hy1 : y 1 = (b, (s (-1)).2) := by
        simp [y, GeneralizedShift.eval_apply, toGeneralizedShift, hs0, hqb, hdir, ShiftDir.toInt]
      have hy_other : ∀ j : ℤ, j ≠ 0 → j ≠ 1 → y j = s (j - 1) := by
        intro j hj0 hj1
        simp only [y, GeneralizedShift.eval_apply, toGeneralizedShift, restrictDom_apply,
          dom3Zero_coe, hs0, hqb, hdir, ShiftDir.toInt, dom3NegOne_coe, dom3One_coe]
        have heq : j + -1 = j - 1 := rfl
        rw [heq]
        by_cases hm : j - 1 ∈ shiftDom3
        · rcases (mem_shiftDom3_iff (j - 1)).mp hm with h | h | h
          · omega
          · omega
          · have hj2 : j = 2 := by omega
            subst hj2
            simp
        · simp [hm]
      simp only [GeneralizedShift.eval_apply, invGeneralizedShift, restrictDom_apply, dom3Zero_coe,
        hy0, hdir, ShiftDir.toInt, neg_neg, dom3One_coe, hy1, hsymm, dom3NegOne_coe]
      by_cases hk1 : k + 1 ∈ shiftDom3
      · rcases (mem_shiftDom3_iff (k + 1)).mp hk1 with h | h | h
        · have hk_eq : k = -2 := by omega
          subst hk_eq
          simpa using hy_other (-1) (by omega) (by omega)
        · have hk_eq : k = -1 := by omega
          subst hk_eq
          simp
        · have hk_eq : k = 0 := by omega
          subst hk_eq
          simp [hs0]
      · obtain ⟨hn1, hn2, hn3⟩ := (notMem_shiftDom3_iff _).mp hk1
        rw [replaceDom_notMem _ _ _ hk1, hy_other (k + 1) (by omega) (by omega)]
        simp
    · have hy0 : y 0 = (b, some q') := by
        simp [y, GeneralizedShift.eval_apply, toGeneralizedShift, hs0, hqb, hdir, ShiftDir.toInt]
      have hy_other : ∀ j : ℤ, j ≠ 0 → y j = s j := by
        intro j hj0
        simp only [y, GeneralizedShift.eval_apply, toGeneralizedShift, restrictDom_apply,
          dom3Zero_coe, hs0, hqb, hdir, ShiftDir.toInt, add_zero, dom3NegOne_coe, dom3One_coe]
        by_cases hm : j ∈ shiftDom3
        · rcases (mem_shiftDom3_iff j).mp hm with rfl | rfl | rfl
          · simp
          · exact (hj0 rfl).elim
          · simp
        · simp [hm]
      simp only [GeneralizedShift.eval_apply, invGeneralizedShift, restrictDom_apply, dom3Zero_coe,
        hy0, hdir, ShiftDir.toInt, neg_zero, add_zero, hsymm, dom3NegOne_coe, dom3One_coe]
      by_cases hk : k ∈ shiftDom3
      · rcases (mem_shiftDom3_iff k).mp hk with rfl | rfl | rfl
        · simpa using hy_other (-1) (by omega)
        · simp [hs0]
        · simpa using hy_other 1 (by omega)
      · obtain ⟨_, hn0, _⟩ := (notMem_shiftDom3_iff _).mp hk
        rw [replaceDom_notMem _ _ _ hk, hy_other k hn0]
    · have hy0 : y 0 = ((s 1).1, some q') := by
        simp [y, GeneralizedShift.eval_apply, toGeneralizedShift, hs0, hqb, hdir, ShiftDir.toInt]
      have hy_neg1 : y (-1) = (b, (s 1).2) := by
        simp [y, GeneralizedShift.eval_apply, toGeneralizedShift, hs0, hqb, hdir, ShiftDir.toInt]
      have hy_other : ∀ j : ℤ, j ≠ 0 → j ≠ -1 → y j = s (j + 1) := by
        intro j hj0 hjn1
        simp only [y, GeneralizedShift.eval_apply, toGeneralizedShift, restrictDom_apply,
          dom3Zero_coe, hs0, hqb, hdir, ShiftDir.toInt, dom3NegOne_coe, dom3One_coe]
        by_cases hm : j + 1 ∈ shiftDom3
        · rcases (mem_shiftDom3_iff (j + 1)).mp hm with h | h | h
          · have hj2 : j = -2 := by omega
            subst hj2
            simp
          · omega
          · omega
        · simp [hm]
      simp only [GeneralizedShift.eval_apply, invGeneralizedShift, restrictDom_apply, dom3Zero_coe,
        hy0, hdir, ShiftDir.toInt, dom3NegOne_coe, hy_neg1, hsymm, dom3One_coe]
      by_cases hk1 : k + -1 ∈ shiftDom3
      · rcases (mem_shiftDom3_iff (k + -1)).mp hk1 with h | h | h
        · have hk_eq : k = 0 := by omega
          subst hk_eq
          simp [hs0]
        · have hk_eq : k = 1 := by omega
          subst hk_eq
          simp
        · have hk_eq : k = 2 := by omega
          subst hk_eq
          simpa using hy_other 1 (by omega) (by omega)
      · obtain ⟨hn1, hn2, hn3⟩ := (notMem_shiftDom3_iff _).mp hk1
        rw [replaceDom_notMem _ _ _ hk1, hy_other (k + -1) (by omega) (by omega)]
        ring_nf

/-- `R.invGeneralizedShift.eval` is a right inverse to `R.toGeneralizedShift.eval` on all of
`ℤ → R.ShiftAlphabet`. -/
theorem to_eval_inv_eval (R : ReversibleTM) (y : ℤ → R.ShiftAlphabet) :
    R.toGeneralizedShift.eval (R.invGeneralizedShift.eval y) = y := by
  funext k
  let s := R.invGeneralizedShift.eval y
  change R.toGeneralizedShift.eval s k = y k
  rcases hy0 : y 0 with ⟨c₀, _ | q'⟩
  · have hs : s = y := by
      funext j
      simp only [s, GeneralizedShift.eval_apply, invGeneralizedShift, restrictDom_apply,
        dom3Zero_coe, hy0, add_zero]
      by_cases hj : j ∈ shiftDom3 <;> simp [hj]
    rw [hs]
    simp only [GeneralizedShift.eval_apply, toGeneralizedShift, restrictDom_apply, dom3Zero_coe,
      hy0, add_zero]
    by_cases hk : k ∈ shiftDom3 <;> simp [hk]
  · rcases hdir : R.dirIn q'
    · generalize hqa : R.stepPerm.symm (q', (y 1).1) = qa
      rcases qa with ⟨q, a₀⟩
      have hfwd : R.stepPerm (q, a₀) = (q', (y 1).1) :=
        R.stepPerm.eq_symm_apply.mp hqa.symm
      have hs0 : s 0 = (a₀, some q) := by
        simp [s, GeneralizedShift.eval_apply, invGeneralizedShift, hy0, hdir, ShiftDir.toInt, hqa]
      have hsn1 : s (-1) = (c₀, (y 1).2) := by
        simp [s, GeneralizedShift.eval_apply, invGeneralizedShift, hy0, hdir, ShiftDir.toInt, hqa]
      have hs_other : ∀ j : ℤ, j ≠ 0 → j ≠ -1 → s j = y (j + 1) := by
        intro j hj0 hjn1
        simp only [s, GeneralizedShift.eval_apply, invGeneralizedShift, restrictDom_apply,
          dom3Zero_coe, hy0, hdir, ShiftDir.toInt, neg_neg, dom3One_coe, hqa, dom3NegOne_coe]
        by_cases hm : j + 1 ∈ shiftDom3
        · rcases (mem_shiftDom3_iff (j + 1)).mp hm with h | h | h
          · have hj2 : j = -2 := by omega
            subst hj2
            simp
          · omega
          · omega
        · simp [hm]
      simp only [GeneralizedShift.eval_apply, toGeneralizedShift, restrictDom_apply, dom3Zero_coe,
        hs0, hfwd, hdir, ShiftDir.toInt, dom3NegOne_coe, hsn1, dom3One_coe]
      by_cases hk1 : k + -1 ∈ shiftDom3
      · rcases (mem_shiftDom3_iff (k + -1)).mp hk1 with h | h | h
        · have hk_eq : k = 0 := by omega
          subst hk_eq
          simp [hy0]
        · have hk_eq : k = 1 := by omega
          subst hk_eq
          simp
        · have hk_eq : k = 2 := by omega
          subst hk_eq
          simpa using hs_other 1 (by omega) (by omega)
      · obtain ⟨hn1, hn2, hn3⟩ := (notMem_shiftDom3_iff _).mp hk1
        rw [replaceDom_notMem _ _ _ hk1, hs_other (k + -1) (by omega) (by omega)]
        ring_nf
    · generalize hqa : R.stepPerm.symm (q', c₀) = qa
      rcases qa with ⟨q, a₀⟩
      have hfwd : R.stepPerm (q, a₀) = (q', c₀) :=
        R.stepPerm.eq_symm_apply.mp hqa.symm
      have hs0 : s 0 = (a₀, some q) := by
        simp [s, GeneralizedShift.eval_apply, invGeneralizedShift, hy0, hdir, ShiftDir.toInt, hqa]
      have hs_other : ∀ j : ℤ, j ≠ 0 → s j = y j := by
        intro j hj0
        simp only [s, GeneralizedShift.eval_apply, invGeneralizedShift, restrictDom_apply,
          dom3Zero_coe, hy0, hdir, ShiftDir.toInt, neg_zero, add_zero, hqa, dom3NegOne_coe,
          dom3One_coe]
        by_cases hm : j ∈ shiftDom3
        · rcases (mem_shiftDom3_iff j).mp hm with rfl | rfl | rfl
          · simp
          · exact (hj0 rfl).elim
          · simp
        · simp [hm]
      simp only [GeneralizedShift.eval_apply, toGeneralizedShift, restrictDom_apply, dom3Zero_coe,
        hs0, hfwd, hdir, ShiftDir.toInt, add_zero, dom3NegOne_coe, dom3One_coe]
      by_cases hk : k ∈ shiftDom3
      · rcases (mem_shiftDom3_iff k).mp hk with rfl | rfl | rfl
        · simpa using hs_other (-1) (by omega)
        · simp [hy0]
        · simpa using hs_other 1 (by omega)
      · obtain ⟨_, hn0, _⟩ := (notMem_shiftDom3_iff _).mp hk
        rw [replaceDom_notMem _ _ _ hk, hs_other k hn0]
    · generalize hqa : R.stepPerm.symm (q', (y (-1)).1) = qa
      rcases qa with ⟨q, a₀⟩
      have hfwd : R.stepPerm (q, a₀) = (q', (y (-1)).1) :=
        R.stepPerm.eq_symm_apply.mp hqa.symm
      have hs0 : s 0 = (a₀, some q) := by
        simp [s, GeneralizedShift.eval_apply, invGeneralizedShift, hy0, hdir, ShiftDir.toInt, hqa]
      have hs1 : s 1 = (c₀, (y (-1)).2) := by
        simp [s, GeneralizedShift.eval_apply, invGeneralizedShift, hy0, hdir, ShiftDir.toInt, hqa]
      have hs_other : ∀ j : ℤ, j ≠ 0 → j ≠ 1 → s j = y (j - 1) := by
        intro j hj0 hj1
        simp only [s, GeneralizedShift.eval_apply, invGeneralizedShift, restrictDom_apply,
          dom3Zero_coe, hy0, hdir, ShiftDir.toInt, dom3NegOne_coe, hqa, dom3One_coe]
        have heq : j + -1 = j - 1 := rfl
        rw [heq]
        by_cases hm : j - 1 ∈ shiftDom3
        · rcases (mem_shiftDom3_iff (j - 1)).mp hm with h | h | h
          · omega
          · omega
          · have hj2 : j = 2 := by omega
            subst hj2
            simp
        · simp [hm]
      simp only [GeneralizedShift.eval_apply, toGeneralizedShift, restrictDom_apply, dom3Zero_coe,
        hs0, hfwd, hdir, ShiftDir.toInt, dom3One_coe, hs1, dom3NegOne_coe]
      by_cases hk1 : k + 1 ∈ shiftDom3
      · rcases (mem_shiftDom3_iff (k + 1)).mp hk1 with h | h | h
        · have hk_eq : k = -2 := by omega
          subst hk_eq
          simpa using hs_other (-1) (by omega) (by omega)
        · have hk_eq : k = -1 := by omega
          subst hk_eq
          simp
        · have hk_eq : k = 0 := by omega
          subst hk_eq
          simp [hy0]
      · obtain ⟨hn1, hn2, hn3⟩ := (notMem_shiftDom3_iff _).mp hk1
        rw [replaceDom_notMem _ _ _ hk1, hs_other (k + 1) (by omega) (by omega)]
        simp

/-- `R.toGeneralizedShift.eval` packaged as a global equivalence `(ℤ → R.ShiftAlphabet) ≃ _`. -/
def toEquiv (R : ReversibleTM) : (ℤ → R.ShiftAlphabet) ≃ (ℤ → R.ShiftAlphabet) where
  toFun := R.toGeneralizedShift.eval
  invFun := R.invGeneralizedShift.eval
  left_inv := R.inv_eval_to_eval
  right_inv := R.to_eval_inv_eval

/-- **`CMPP21` Proposition 4.4 (Reversible Bijectivity)**: the generalized shift associated to any
unidirectional reversible Turing machine `R` is bijective on `ℤ → R.ShiftAlphabet`. -/
theorem bijective_eval (R : ReversibleTM) : Function.Bijective R.toGeneralizedShift.eval :=
  R.toEquiv.bijective

/-- Exact single-step conjugacy between `R.step` and `R.toGeneralizedShift.eval` (`CMPP21`
Proposition 4.4). -/
theorem eval_encodeCfg (R : ReversibleTM) (c : R.Cfg) :
    R.toGeneralizedShift.eval (R.encodeCfg c) = R.encodeCfg (R.step c) := by
  rcases c with ⟨q, T⟩
  funext k
  have hhead : T.nth 0 = T.head := rfl
  simp only [GeneralizedShift.eval_apply, toGeneralizedShift, encodeCfg, restrictDom_apply,
    dom3Zero_coe, ↓reduceIte, hhead, step]
  generalize hqb : R.stepPerm (q, T.head) = qb
  rcases qb with ⟨q', b⟩
  rcases hdir : R.dirIn q'
  · simp only [ShiftDir.toInt, dom3NegOne_coe, dom3One_coe]
    by_cases hk : k + -1 ∈ shiftDom3
    · rcases (mem_shiftDom3_iff (k + -1)).mp hk with h | h | h
      · have hk_eq : k = 0 := by omega
        subst hk_eq
        simp
      · have hk_eq : k = 1 := by omega
        subst hk_eq
        simp
      · have hk_eq : k = 2 := by omega
        subst hk_eq
        simp
    · obtain ⟨hn1, hn2, hn3⟩ := (notMem_shiftDom3_iff _).mp hk
      rw [replaceDom_notMem _ _ _ hk]
      have hk0 : k ≠ 0 := by omega
      simp [encodeCfg, hk0, hn2, sub_eq_add_neg]
  · simp only [ShiftDir.toInt, add_zero, dom3NegOne_coe, dom3One_coe]
    by_cases hk : k ∈ shiftDom3
    · rcases (mem_shiftDom3_iff k).mp hk with rfl | rfl | rfl <;> simp
    · obtain ⟨_, hn0, _⟩ := (notMem_shiftDom3_iff _).mp hk
      rw [replaceDom_notMem _ _ _ hk]
      simp [encodeCfg, hn0]
  · simp only [ShiftDir.toInt, dom3NegOne_coe, dom3One_coe]
    by_cases hk : k + 1 ∈ shiftDom3
    · rcases (mem_shiftDom3_iff (k + 1)).mp hk with h | h | h
      · have hk_eq : k = -2 := by omega
        subst hk_eq
        simp
      · have hk_eq : k = -1 := by omega
        subst hk_eq
        simp
      · have hk_eq : k = 0 := by omega
        subst hk_eq
        simp
    · obtain ⟨hn1, hn2, hn3⟩ := (notMem_shiftDom3_iff _).mp hk
      rw [replaceDom_notMem _ _ _ hk]
      have hk0 : k ≠ 0 := by omega
      simp [encodeCfg, hk0, hn2]

/-- Iterated orbit conjugacy for `ReversibleTM`. -/
theorem iterate_eval_encodeCfg (R : ReversibleTM) (c : R.Cfg) (n : ℕ) :
    R.toGeneralizedShift.eval^[n] (R.encodeCfg c) = R.encodeCfg (R.step^[n] c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, R.eval_encodeCfg, ih, Function.iterate_succ_apply]

end ReversibleTM

/-! ## 3. `FinTM0` Conjugacy on `{-1, 0, 1}` & `HaltsWithWindow` Equivalence (`CMPP21` Prop. 4.4) -/

/-- Cylinder set in `ℤ → A` determined by a finite window `w : Set.Icc (-k) k → A`. -/
def cylinderIcc {A : Type*} (k : ℕ) (w : Set.Icc (-(k : ℤ)) (k : ℤ) → A) : Set (ℤ → A) :=
  { s : ℤ → A | ∀ i : Set.Icc (-(k : ℤ)) (k : ℤ), s i.1 = w i }

theorem cylinderIcc_nonempty {A : Type*} [Inhabited A] (k : ℕ)
    (w : Set.Icc (-(k : ℤ)) (k : ℤ) → A) : (cylinderIcc k w).Nonempty :=
  ⟨fun i ↦ if hi : i ∈ Set.Icc (-(k : ℤ)) (k : ℤ) then w ⟨i, hi⟩ else default,
    fun ⟨_, hi⟩ ↦ by simp [hi]⟩

namespace FinTM0

/-- Finite shift alphabet `M.Γ × Option (Option M.Λ)` for `M : FinTM0`:
* `none` at cell `i` means the head is not at `i`;
* `some (some q)` at cell `0` means the head is active in state `q : M.Λ`;
* `some none` at cell `0` represents the dedicated terminal/halted state on the final tape. -/
abbrev ShiftAlphabet (M : FinTM0) : Type :=
  M.Γ × Option (Option M.Λ)

/-- Encode an active `TM0` configuration `c` into `ℤ → M.ShiftAlphabet`. -/
def encodeActiveCfg (M : FinTM0) (c : Turing.TM0.Cfg M.Γ M.Λ) : ℤ → M.ShiftAlphabet :=
  fun i ↦ (c.Tape.nth i, if i = 0 then some (some c.q) else none)

/-- Encode a halted `TM0` tape `T` into `ℤ → M.ShiftAlphabet` using the terminal marker
`some none` at cell `0`. -/
def encodeHaltedTape (M : FinTM0) (T : Turing.Tape M.Γ) : ℤ → M.ShiftAlphabet :=
  fun i ↦ (T.nth i, if i = 0 then some none else none)

/-- Initial shift sequence encoding `M.initCfg t` (`{ q := default, Tape := t }`). -/
def encodeInit (M : FinTM0) (t : FinSupportedTape M) : ℤ → M.ShiftAlphabet :=
  M.encodeActiveCfg (M.initCfg t)

/-- Target cylinder block on `[-k, k]` witnessing halting (`some none` at `0`) with output window
`w` on `[-k, k]`. -/
def haltWindow (M : FinTM0) (k : ℕ) (w : Window M k) :
    Set.Icc (-(k : ℤ)) (k : ℤ) → M.ShiftAlphabet :=
  fun i ↦ (w i, if i.1 = 0 then some none else none)

/-- Generalized shift on `D_F = D_G = {-1, 0, 1}` simulating `M : FinTM0` (`CMPP21`
Proposition 4.4). Active configurations execute `Turing.TM0.step M.machine`; when
`M.machine q a = none`, cell `0` transitions in one step to `(a, some none)` and thereafter remains
fixed on the terminal tape. -/
def toGeneralizedShift (M : FinTM0) : GeneralizedShift M.ShiftAlphabet where
  D := shiftDom3
  F w :=
    match (w dom3Zero).2 with
    | none => 0
    | some none => 0
    | some (some q) =>
      match M.machine q (w dom3Zero).1 with
      | none => 0
      | some (_, Turing.TM0.Stmt.write _) => 0
      | some (_, Turing.TM0.Stmt.move Turing.Dir.left) => -1
      | some (_, Turing.TM0.Stmt.move Turing.Dir.right) => 1
  G w :=
    match (w dom3Zero).2 with
    | none => w
    | some none => w
    | some (some q) =>
      match M.machine q (w dom3Zero).1 with
      | none =>
        mkDom3 (w dom3NegOne) ((w dom3Zero).1, some none) (w dom3One)
      | some (q', Turing.TM0.Stmt.write b) =>
        mkDom3 (w dom3NegOne) (b, some (some q')) (w dom3One)
      | some (q', Turing.TM0.Stmt.move Turing.Dir.left) =>
        mkDom3 ((w dom3NegOne).1, some (some q')) ((w dom3Zero).1, none) (w dom3One)
      | some (q', Turing.TM0.Stmt.move Turing.Dir.right) =>
        mkDom3 (w dom3NegOne) ((w dom3Zero).1, none) ((w dom3One).1, some (some q'))

@[simp]
theorem toGeneralizedShift_D (M : FinTM0) : M.toGeneralizedShift.D = shiftDom3 :=
  rfl

/-- One-step simulation when `Turing.TM0.step M.machine c = some c'`. -/
theorem eval_encodeActiveCfg_of_step_eq_some (M : FinTM0)
    {c c' : Turing.TM0.Cfg M.Γ M.Λ} (hstep : Turing.TM0.step M.machine c = some c') :
    M.toGeneralizedShift.eval (M.encodeActiveCfg c) = M.encodeActiveCfg c' := by
  rcases c with ⟨q, T⟩
  have hhead : T.nth 0 = T.1 := rfl
  simp only [Turing.TM0.step] at hstep
  rcases hm : M.machine q T.1 with _ | ⟨q', stmt⟩
  · simp [hm] at hstep
  · simp only [hm, Option.map_some, Option.some.injEq] at hstep
    subst hstep
    funext k
    rcases stmt with (_ | _) | b
    · simp only [GeneralizedShift.eval_apply, toGeneralizedShift, encodeActiveCfg,
        restrictDom_apply, dom3Zero_coe, ↓reduceIte, hhead, hm, dom3NegOne_coe, dom3One_coe]
      by_cases hk : k + -1 ∈ shiftDom3
      · rcases (mem_shiftDom3_iff (k + -1)).mp hk with h | h | h
        · have hk_eq : k = 0 := by omega
          subst hk_eq
          simp
        · have hk_eq : k = 1 := by omega
          subst hk_eq
          simp [hhead]
        · have hk_eq : k = 2 := by omega
          subst hk_eq
          simp
      · obtain ⟨hn1, hn2, hn3⟩ := (notMem_shiftDom3_iff _).mp hk
        rw [replaceDom_notMem _ _ _ hk]
        have hk0 : k ≠ 0 := by omega
        simp [encodeActiveCfg, hk0, hn2, sub_eq_add_neg]
    · simp only [GeneralizedShift.eval_apply, toGeneralizedShift, encodeActiveCfg,
        restrictDom_apply, dom3Zero_coe, ↓reduceIte, hhead, hm, dom3NegOne_coe, dom3One_coe]
      by_cases hk : k + 1 ∈ shiftDom3
      · rcases (mem_shiftDom3_iff (k + 1)).mp hk with h | h | h
        · have hk_eq : k = -2 := by omega
          subst hk_eq
          simp
        · have hk_eq : k = -1 := by omega
          subst hk_eq
          simp [hhead]
        · have hk_eq : k = 0 := by omega
          subst hk_eq
          simp
      · obtain ⟨hn1, hn2, hn3⟩ := (notMem_shiftDom3_iff _).mp hk
        rw [replaceDom_notMem _ _ _ hk]
        have hk0 : k ≠ 0 := by omega
        simp [encodeActiveCfg, hk0, hn2]
    · simp only [GeneralizedShift.eval_apply, toGeneralizedShift, encodeActiveCfg,
        restrictDom_apply, dom3Zero_coe, ↓reduceIte, hhead, hm, add_zero, dom3NegOne_coe,
        dom3One_coe]
      by_cases hk : k ∈ shiftDom3
      · rcases (mem_shiftDom3_iff k).mp hk with rfl | rfl | rfl <;> simp
      · obtain ⟨_, hn0, _⟩ := (notMem_shiftDom3_iff _).mp hk
        rw [replaceDom_notMem _ _ _ hk]
        simp [encodeActiveCfg, hn0]

/-- When `Turing.TM0.step M.machine c = none`, one generalized-shift step transitions
`M.encodeActiveCfg c` to `M.encodeHaltedTape c.Tape`. -/
theorem eval_encodeActiveCfg_of_step_eq_none (M : FinTM0)
    {c : Turing.TM0.Cfg M.Γ M.Λ} (hstep : Turing.TM0.step M.machine c = none) :
    M.toGeneralizedShift.eval (M.encodeActiveCfg c) = M.encodeHaltedTape c.Tape := by
  rcases c with ⟨q, T⟩
  have hhead : T.nth 0 = T.1 := rfl
  simp only [Turing.TM0.step, Option.map_eq_none_iff] at hstep
  funext k
  simp only [GeneralizedShift.eval_apply, toGeneralizedShift, encodeActiveCfg, encodeHaltedTape,
    restrictDom_apply, dom3Zero_coe, ↓reduceIte, hhead, hstep, add_zero, dom3NegOne_coe,
    dom3One_coe]
  by_cases hk : k ∈ shiftDom3
  · rcases (mem_shiftDom3_iff k).mp hk with rfl | rfl | rfl <;> simp [hhead]
  · obtain ⟨_, hn0, _⟩ := (notMem_shiftDom3_iff _).mp hk
    rw [replaceDom_notMem _ _ _ hk]
    simp [encodeActiveCfg, hn0]

/-- Halted tape configurations are fixed points of `M.toGeneralizedShift.eval`. -/
@[simp]
theorem eval_encodeHaltedTape (M : FinTM0) (T : Turing.Tape M.Γ) :
    M.toGeneralizedShift.eval (M.encodeHaltedTape T) = M.encodeHaltedTape T := by
  funext k
  simp only [GeneralizedShift.eval_apply, toGeneralizedShift, encodeHaltedTape, restrictDom_apply,
    dom3Zero_coe, ↓reduceIte, add_zero]
  by_cases hk : k ∈ shiftDom3
  · simp [hk, encodeHaltedTape]
  · simp [hk, encodeHaltedTape]

@[simp]
theorem iterate_eval_encodeHaltedTape (M : FinTM0) (T : Turing.Tape M.Γ) (n : ℕ) :
    M.toGeneralizedShift.eval^[n] (M.encodeHaltedTape T) = M.encodeHaltedTape T := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, M.eval_encodeHaltedTape]

/-- Multi-step active simulation: while `M.stepOpt^[n] (some c₀) = some c`, the `n`-th iterate of
`M.toGeneralizedShift.eval` equals `M.encodeActiveCfg c`. -/
theorem iterate_eval_encodeActiveCfg_of_stepOpt (M : FinTM0)
    {c₀ c : Turing.TM0.Cfg M.Γ M.Λ} {n : ℕ} (hn : M.stepOpt^[n] (some c₀) = some c) :
    M.toGeneralizedShift.eval^[n] (M.encodeActiveCfg c₀) = M.encodeActiveCfg c := by
  induction n generalizing c₀ with
  | zero =>
    cases hn
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply] at hn ⊢
    change M.stepOpt^[n] (Turing.TM0.step M.machine c₀) = some c at hn
    rcases h1 : Turing.TM0.step M.machine c₀ with _ | c₁
    · rw [h1, M.iterate_stepOpt_none] at hn
      cases hn
    · rw [h1] at hn
      rw [M.eval_encodeActiveCfg_of_step_eq_some h1]
      exact ih hn

/-- Complete orbit dichotomy for `M.toGeneralizedShift.eval^[n] (M.encodeActiveCfg c₀)`:
at step `n`, either `M` is still active (`M.stepOpt^[n] (some c₀) = some c`), or `M` halted at some
step `m < n` at terminal configuration `c` (`M.stepOpt^[m] (some c₀) = some c` and `step c = none`)
and the shift sequence equals `M.encodeHaltedTape c.Tape`. -/
theorem iterate_eval_encodeActiveCfg_dichotomy (M : FinTM0) (c₀ : Turing.TM0.Cfg M.Γ M.Λ)
    (n : ℕ) :
    (∃ c, M.stepOpt^[n] (some c₀) = some c ∧
      M.toGeneralizedShift.eval^[n] (M.encodeActiveCfg c₀) = M.encodeActiveCfg c) ∨
    (∃ m c, m < n ∧ M.stepOpt^[m] (some c₀) = some c ∧ Turing.TM0.step M.machine c = none ∧
      M.toGeneralizedShift.eval^[n] (M.encodeActiveCfg c₀) = M.encodeHaltedTape c.Tape) := by
  induction n with
  | zero =>
    exact Or.inl ⟨c₀, rfl, rfl⟩
  | succ n ih =>
    rcases ih with ⟨c, hn, heq⟩ | ⟨m, c, hmn, hm, hterm, heq⟩
    · rcases hstep : Turing.TM0.step M.machine c with _ | c'
      · refine Or.inr ⟨n, c, Nat.lt_succ_self n, hn, hstep, ?_⟩
        rw [Function.iterate_succ_apply', heq, M.eval_encodeActiveCfg_of_step_eq_none hstep]
      · refine Or.inl ⟨c', ?_, ?_⟩
        · rw [Function.iterate_succ_apply', hn]
          exact hstep
        · rw [Function.iterate_succ_apply', heq, M.eval_encodeActiveCfg_of_step_eq_some hstep]
    · refine Or.inr ⟨m, c, Nat.lt_succ_of_lt hmn, hm, hterm, ?_⟩
      rw [Function.iterate_succ_apply', heq, M.eval_encodeHaltedTape]

/-- No active configuration ever lies in `cylinderIcc k (M.haltWindow k w)`. -/
theorem encodeActiveCfg_notMem_haltCylinder (M : FinTM0) (c : Turing.TM0.Cfg M.Γ M.Λ)
    (k : ℕ) (w : Window M k) :
    M.encodeActiveCfg c ∉ cylinderIcc k (M.haltWindow k w) := by
  intro hmem
  have h0 : (0 : ℤ) ∈ Set.Icc (-(k : ℤ)) (k : ℤ) := ⟨by omega, by omega⟩
  have h := congrArg Prod.snd (hmem ⟨0, h0⟩)
  simp [encodeActiveCfg, haltWindow] at h

/-- Initial configurations never lie in `cylinderIcc k (M.haltWindow k w)` at `n = 0`. -/
theorem encodeInit_notMem_haltCylinder (M : FinTM0) (t : FinSupportedTape M) (k : ℕ)
    (w : Window M k) :
    M.encodeInit t ∉ cylinderIcc k (M.haltWindow k w) :=
  M.encodeActiveCfg_notMem_haltCylinder (M.initCfg t) k w

/-- Membership of `M.encodeHaltedTape T` in `cylinderIcc k (M.haltWindow k w)` is equivalent to
agreement of `T` with `w` on `[-k, k]`. -/
theorem encodeHaltedTape_mem_haltCylinder_iff (M : FinTM0) (T : Turing.Tape M.Γ) (k : ℕ)
    (w : Window M k) :
    M.encodeHaltedTape T ∈ cylinderIcc k (M.haltWindow k w) ↔
      ∀ i : Set.Icc (-(k : ℤ)) (k : ℤ), T.nth i.1 = w i := by
  constructor
  · intro h i
    exact congrArg Prod.fst (h i)
  · intro h i
    exact Prod.ext (h i) rfl

/-- **`CMPP21` Proposition 4.4 (`HaltsWithWindow` Equivalence)**: the forward orbit of
`M.encodeInit t` under `M.toGeneralizedShift.eval` enters `cylinderIcc k (M.haltWindow k w)` if and
only if `HaltsWithWindow M t k w`. -/
theorem orbit_mem_haltCylinder_iff_haltsWithWindow (M : FinTM0) (t : FinSupportedTape M)
    (k : ℕ) (w : Window M k) :
    (∃ n : ℕ, M.toGeneralizedShift.eval^[n] (M.encodeInit t) ∈
        cylinderIcc k (M.haltWindow k w)) ↔
      HaltsWithWindow M t k w := by
  rw [haltsWithWindow_iff_exists_steps]
  constructor
  · rintro ⟨n, hmem⟩
    rcases M.iterate_eval_encodeActiveCfg_dichotomy (M.initCfg t) n with
      ⟨c, _, heq⟩ | ⟨m, c, _, hm, hterm, heq⟩
    · rw [encodeInit, heq] at hmem
      exact (M.encodeActiveCfg_notMem_haltCylinder c k w hmem).elim
    · rw [encodeInit, heq, M.encodeHaltedTape_mem_haltCylinder_iff] at hmem
      exact ⟨m, c, hm, hterm, hmem⟩
  · rintro ⟨m, c, hm, hterm, hwin⟩
    refine ⟨m + 1, ?_⟩
    rw [encodeInit, Function.iterate_succ_apply',
      M.iterate_eval_encodeActiveCfg_of_stepOpt hm,
      M.eval_encodeActiveCfg_of_step_eq_none hterm,
      M.encodeHaltedTape_mem_haltCylinder_iff]
    exact hwin

end FinTM0

/-! ## 4. Odd-Base Square Cantor Embedding `(ℤ → A) ↪ UnitDisk2` & `Computable` Approximations -/

/-- Odd Cantor base `max (2 * N - 1) 3`: equals `2 * N - 1` whenever `N ≥ 2` (`CMPP21` Section 4.2)
and stays `≥ 3` for degenerate small alphabets `N ≤ 1`. -/
def cantorBase (N : ℕ) : ℕ :=
  max (2 * N - 1) 3

theorem cantorBase_eq_of_two_le {N : ℕ} (hN : 2 ≤ N) : cantorBase N = 2 * N - 1 := by
  unfold cantorBase
  omega

theorem three_le_cantorBase (N : ℕ) : 3 ≤ cantorBase N :=
  le_max_right _ _

theorem cantorBase_pos (N : ℕ) : 0 < cantorBase N :=
  lt_of_lt_of_le (by decide : 0 < 3) (three_le_cantorBase N)

/-- Map a digit `d : Fin N` to the even digit `2 * d < cantorBase N`, leaving odd gaps between
distinct subintervals. -/
def cantorEvenDigit {N : ℕ} (d : Fin N) : Fin (cantorBase N) :=
  ⟨2 * d.1, by
    have hd := d.2
    unfold cantorBase
    omega⟩

/-- Integer numerator `∑_{j=0}^{m-1} (2 w_j) B^{m - 1 - j}` of the finite middle-Cantor prefix
of length `m`. -/
def cantorPrefixCode (B : ℕ) : {m : ℕ} → (Fin m → ℕ) → ℕ
  | 0, _ => 0
  | m + 1, w => B * cantorPrefixCode B (fun j : Fin m ↦ w j.castSucc) + 2 * w (Fin.last m)

theorem cantorPrefixCode_add_one_le_pow (B : ℕ) (hB : 1 ≤ B) :
    ∀ {m : ℕ} (w : Fin m → ℕ), (∀ j : Fin m, 2 * w j ≤ B - 1) →
      cantorPrefixCode B w + 1 ≤ B ^ m
  | 0, _, _ => by simp [cantorPrefixCode]
  | m + 1, w, hw => by
    have ih := cantorPrefixCode_add_one_le_pow B hB (fun j : Fin m ↦ w j.castSucc)
      (fun j ↦ hw j.castSucc)
    have hlast : 2 * w (Fin.last m) + 1 ≤ B := by
      have := hw (Fin.last m)
      omega
    calc
      cantorPrefixCode B w + 1
          = B * cantorPrefixCode B (fun j : Fin m ↦ w j.castSucc) + (2 * w (Fin.last m) + 1) := by
            simp [cantorPrefixCode, add_assoc]
      _ ≤ B * cantorPrefixCode B (fun j : Fin m ↦ w j.castSucc) + B :=
            Nat.add_le_add_left hlast _
      _ = B * (cantorPrefixCode B (fun j : Fin m ↦ w j.castSucc) + 1) := by ring
      _ ≤ B * B ^ m := Nat.mul_le_mul_left B ih
      _ = B ^ (m + 1) := (pow_succ' B m).symm

theorem cantorPrefixCode_le_pow_sub_one (B : ℕ) (hB : 1 ≤ B) {m : ℕ} (w : Fin m → ℕ)
    (hw : ∀ j : Fin m, 2 * w j ≤ B - 1) :
    cantorPrefixCode B w ≤ B ^ m - 1 := by
  have h := cantorPrefixCode_add_one_le_pow B hB w hw
  omega

/-- Any two distinct prefixes `w₁ ≠ w₂` of length `m` with `2 * w_j ≤ B - 1` and `B ≥ 3` have
integer prefix codes separated by at least `2`. -/
theorem two_le_abs_cantorPrefixCode_sub {B : ℕ} (hB : 3 ≤ B) :
    ∀ {m : ℕ} {w₁ w₂ : Fin m → ℕ},
      w₁ ≠ w₂ →
      (∀ j : Fin m, 2 * w₁ j ≤ B - 1) →
      (∀ j : Fin m, 2 * w₂ j ≤ B - 1) →
      (2 : ℤ) ≤ |(cantorPrefixCode B w₁ : ℤ) - (cantorPrefixCode B w₂ : ℤ)|
  | 0, w₁, w₂, hne, _, _ => (hne (Subsingleton.elim w₁ w₂)).elim
  | m + 1, w₁, w₂, hne, hw₁, hw₂ => by
    let w₁' : Fin m → ℕ := fun j ↦ w₁ j.castSucc
    let w₂' : Fin m → ℕ := fun j ↦ w₂ j.castSucc
    change (2 : ℤ) ≤
      |((B * cantorPrefixCode B w₁' + 2 * w₁ (Fin.last m) : ℕ) : ℤ) -
        ((B * cantorPrefixCode B w₂' + 2 * w₂ (Fin.last m) : ℕ) : ℤ)|
    push_cast
    by_cases hinit : w₁' = w₂'
    · have hlast_ne : w₁ (Fin.last m) ≠ w₂ (Fin.last m) := by
        intro hlast
        apply hne
        funext j
        exact Fin.lastCases (motive := fun j ↦ w₁ j = w₂ j) hlast (fun i ↦ congrFun hinit i) j
      rw [hinit, add_sub_add_left_eq_sub]
      rcases lt_or_gt_of_ne hlast_ne with hlt | hgt
      · rw [abs_of_neg (by omega)]
        omega
      · rw [abs_of_pos (by omega)]
        omega
    · have ih := two_le_abs_cantorPrefixCode_sub hB hinit
        (fun j ↦ hw₁ j.castSucc) (fun j ↦ hw₂ j.castSucc)
      have hb₁ : 2 * (w₁ (Fin.last m) : ℤ) ≤ (B : ℤ) - 1 := by
        have := hw₁ (Fin.last m)
        omega
      have hb₂ : 2 * (w₂ (Fin.last m) : ℤ) ≤ (B : ℤ) - 1 := by
        have := hw₂ (Fin.last m)
        omega
      set d_init : ℤ := (cantorPrefixCode B w₁' : ℤ) - (cantorPrefixCode B w₂' : ℤ)
      set d_last : ℤ := 2 * (w₁ (Fin.last m) : ℤ) - 2 * (w₂ (Fin.last m) : ℤ)
      have hrew :
          ((B : ℤ) * (cantorPrefixCode B w₁' : ℤ) + 2 * (w₁ (Fin.last m) : ℤ)) -
            ((B : ℤ) * (cantorPrefixCode B w₂' : ℤ) + 2 * (w₂ (Fin.last m) : ℤ)) =
          (B : ℤ) * d_init + d_last := by ring
      rw [hrew]
      have hlast_abs : -(B : ℤ) + 1 ≤ d_last ∧ d_last ≤ (B : ℤ) - 1 := by
        dsimp [d_last]
        omega
      rcases le_or_gt 0 d_init with hd | hd
      · have hd2 : 2 ≤ d_init := by
          rwa [abs_of_nonneg hd] at ih
        have hpos : (B : ℤ) + 1 ≤ (B : ℤ) * d_init + d_last := by nlinarith
        rw [abs_of_nonneg (by linarith)]
        linarith
      · have hd2 : d_init ≤ -2 := by
          rw [abs_of_neg hd] at ih
          linarith
        have hneg : (B : ℤ) * d_init + d_last ≤ -((B : ℤ) + 1) := by nlinarith
        rw [abs_of_neg (by linarith)]
        linarith

/-- One-sided middle-Cantor coordinate in `[0, 1]` built via `Real.ofDigits` in base
`cantorBase N`. -/
noncomputable def cantorCoord {N : ℕ} (α : ℕ → Fin N) : ℝ :=
  Real.ofDigits (fun i ↦ cantorEvenDigit (α i))

theorem cantorCoord_nonneg {N : ℕ} (α : ℕ → Fin N) : 0 ≤ cantorCoord α :=
  Real.ofDigits_nonneg _

theorem cantorCoord_le_one {N : ℕ} (α : ℕ → Fin N) : cantorCoord α ≤ 1 :=
  Real.ofDigits_le_one _

theorem continuous_cantorCoord {N : ℕ} : Continuous (@cantorCoord N) := by
  unfold cantorCoord
  refine Real.continuous_ofDigits.comp (continuous_pi fun i ↦ ?_)
  exact (continuous_of_discreteTopology (f := @cantorEvenDigit N)).comp (continuous_apply i)

theorem sum_ofDigitsTerm_cantorEvenDigit {N : ℕ} (α : ℕ → Fin N) (m : ℕ) :
    (∑ i ∈ Finset.range m, Real.ofDigitsTerm (fun j ↦ cantorEvenDigit (α j)) i) =
      (cantorPrefixCode (cantorBase N) (fun j : Fin m ↦ (α j.1).1) : ℝ) /
        ((cantorBase N : ℝ) ^ m) := by
  have hB0 : (cantorBase N : ℝ) ≠ 0 := by exact_mod_cast (cantorBase_pos N).ne'
  induction m with
  | zero => simp [cantorPrefixCode]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Real.ofDigitsTerm, cantorEvenDigit, cantorPrefixCode, Fin.val_last,
      Fin.val_castSucc, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
    field_simp [hB0]

/-- Exact finite-prefix + tail decomposition of `cantorCoord`. -/
theorem cantorCoord_eq_prefix_add_tail {N : ℕ} (α : ℕ → Fin N) (m : ℕ) :
    cantorCoord α =
      (cantorPrefixCode (cantorBase N) (fun j : Fin m ↦ (α j.1).1) : ℝ) /
        ((cantorBase N : ℝ) ^ m) +
      ((cantorBase N : ℝ) ^ m)⁻¹ * cantorCoord (fun i ↦ α (i + m)) := by
  unfold cantorCoord
  rw [Real.ofDigits_eq_sum_add_ofDigits _ m, sum_ofDigitsTerm_cantorEvenDigit]

theorem prefix_div_le_cantorCoord {N : ℕ} (α : ℕ → Fin N) (m : ℕ) :
    (cantorPrefixCode (cantorBase N) (fun j : Fin m ↦ (α j.1).1) : ℝ) /
        ((cantorBase N : ℝ) ^ m) ≤
      cantorCoord α := by
  rw [cantorCoord_eq_prefix_add_tail α m]
  have h1 : 0 ≤ ((cantorBase N : ℝ) ^ m)⁻¹ := by positivity
  have h2 : 0 ≤ cantorCoord (fun i ↦ α (i + m)) := cantorCoord_nonneg _
  linarith [mul_nonneg h1 h2]

theorem cantorCoord_le_prefix_add_one_div {N : ℕ} (α : ℕ → Fin N) (m : ℕ) :
    cantorCoord α ≤
      ((cantorPrefixCode (cantorBase N) (fun j : Fin m ↦ (α j.1).1) : ℝ) + 1) /
        ((cantorBase N : ℝ) ^ m) := by
  rw [cantorCoord_eq_prefix_add_tail α m, add_div, one_div]
  have h1 : 0 ≤ ((cantorBase N : ℝ) ^ m)⁻¹ := by positivity
  have h2 : cantorCoord (fun i ↦ α (i + m)) ≤ 1 := cantorCoord_le_one _
  have hmul : ((cantorBase N : ℝ) ^ m)⁻¹ * cantorCoord (fun i ↦ α (i + m)) ≤
      ((cantorBase N : ℝ) ^ m)⁻¹ * 1 :=
    mul_le_mul_of_nonneg_left h2 h1
  linarith

/-- Rescaled one-sided Cantor coordinate `(1 / 4) * cantorCoord α ∈ [0, 1/4] ⊂ (-1/2, 1/2)`. -/
noncomputable def scaledCantorCoord {N : ℕ} (α : ℕ → Fin N) : ℝ :=
  (1 / 4 : ℝ) * cantorCoord α

theorem continuous_scaledCantorCoord {N : ℕ} : Continuous (@scaledCantorCoord N) :=
  continuous_const.mul continuous_cantorCoord

theorem scaledCantorCoord_mem_Icc {N : ℕ} (α : ℕ → Fin N) :
    scaledCantorCoord α ∈ Set.Icc (0 : ℝ) (1 / 4) :=
  ⟨by unfold scaledCantorCoord; linarith [cantorCoord_nonneg α],
    by unfold scaledCantorCoord; linarith [cantorCoord_le_one α]⟩

/-- Open interval around the rescaled middle-Cantor block for prefix `w : Fin m → Fin N`.
Expanding `[K, K + 1]` slightly into `(K - 1/3, K + 4/3)` makes the interval open and nonempty
while keeping distinct prefixes pairwise disjoint inside `(-1/2, 1/2)`. -/
noncomputable def cantorOpenInterval {N m : ℕ} (w : Fin m → Fin N) : Set ℝ :=
  let B : ℝ := (cantorBase N : ℝ)
  let K : ℝ := (cantorPrefixCode (cantorBase N) (fun j ↦ (w j).1) : ℝ)
  Set.Ioo ((K - 1 / 3) / (4 * B ^ m)) ((K + 4 / 3) / (4 * B ^ m))

theorem isOpen_cantorOpenInterval {N m : ℕ} (w : Fin m → Fin N) :
    IsOpen (cantorOpenInterval w) :=
  isOpen_Ioo

theorem cantorOpenInterval_nonempty {N m : ℕ} (w : Fin m → Fin N) :
    (cantorOpenInterval w).Nonempty := by
  unfold cantorOpenInterval
  refine Set.nonempty_Ioo.mpr ?_
  have hden : 0 < (4 : ℝ) * (cantorBase N : ℝ) ^ m := by
    have := cantorBase_pos N
    positivity
  exact div_lt_div_of_pos_right (by linarith) hden

theorem cantorOpenInterval_subset_Ioo_half {N m : ℕ} (w : Fin m → Fin N) :
    cantorOpenInterval w ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
  intro x hx
  unfold cantorOpenInterval at hx
  have hB3 : 3 ≤ cantorBase N := three_le_cantorBase N
  have hBm1 : (1 : ℝ) ≤ (cantorBase N : ℝ) ^ m :=
    one_le_pow₀ (by exact_mod_cast le_trans (by decide : 1 ≤ 3) hB3)
  have hden : 0 < (4 : ℝ) * (cantorBase N : ℝ) ^ m := by positivity
  have hK_add := cantorPrefixCode_add_one_le_pow (cantorBase N) (by omega)
    (fun j : Fin m ↦ (w j).1) (fun j ↦ by have := (w j).2; unfold cantorBase; omega)
  have hK_real : (cantorPrefixCode (cantorBase N) (fun j ↦ (w j).1) : ℝ) + 1 ≤
      (cantorBase N : ℝ) ^ m := by
    exact_mod_cast hK_add
  constructor
  · have hlow : -(1 / 2 : ℝ) ≤ ((cantorPrefixCode (cantorBase N) (fun j ↦ (w j).1) : ℝ) - 1 / 3) /
        (4 * (cantorBase N : ℝ) ^ m) := by
      rw [le_div_iff₀ hden]
      have hK0 : (0 : ℝ) ≤ cantorPrefixCode (cantorBase N) (fun j ↦ (w j).1) := Nat.cast_nonneg _
      linarith
    exact lt_of_le_of_lt hlow hx.1
  · have hhigh : ((cantorPrefixCode (cantorBase N) (fun j ↦ (w j).1) : ℝ) + 4 / 3) /
        (4 * (cantorBase N : ℝ) ^ m) ≤ 1 / 2 := by
      rw [div_le_iff₀ hden]
      linarith
    exact lt_of_lt_of_le hx.2 hhigh

/-- Distinct prefixes of the same length map to pairwise disjoint open intervals. -/
theorem disjoint_cantorOpenInterval {N m : ℕ} {w₁ w₂ : Fin m → Fin N} (hne : w₁ ≠ w₂) :
    Disjoint (cantorOpenInterval w₁) (cantorOpenInterval w₂) := by
  rw [Set.disjoint_iff]
  rintro x ⟨hx₁, hx₂⟩
  unfold cantorOpenInterval at hx₁ hx₂
  have hden : 0 < (4 : ℝ) * (cantorBase N : ℝ) ^ m := by
    have := cantorBase_pos N
    positivity
  have hfn_ne : (fun j : Fin m ↦ (w₁ j).1) ≠ (fun j : Fin m ↦ (w₂ j).1) := by
    intro heq
    apply hne
    funext j
    exact Fin.ext (congrFun heq j)
  have hsep := two_le_abs_cantorPrefixCode_sub (three_le_cantorBase N) hfn_ne
    (fun j ↦ by have := (w₁ j).2; unfold cantorBase; omega)
    (fun j ↦ by have := (w₂ j).2; unfold cantorBase; omega)
  let c₁ : ℕ := cantorPrefixCode (cantorBase N) (fun j ↦ (w₁ j).1)
  let c₂ : ℕ := cantorPrefixCode (cantorBase N) (fun j ↦ (w₂ j).1)
  change (2 : ℤ) ≤ |(c₁ : ℤ) - (c₂ : ℤ)| at hsep
  set K₁ : ℝ := (c₁ : ℝ)
  set K₂ : ℝ := (c₂ : ℝ)
  have h₁l := (div_lt_iff₀ hden).mp hx₁.1
  have h₁r := (lt_div_iff₀ hden).mp hx₁.2
  have h₂l := (div_lt_iff₀ hden).mp hx₂.1
  have h₂r := (lt_div_iff₀ hden).mp hx₂.2
  rcases le_or_gt c₂ c₁ with hle | hlt
  · have hc : c₂ + 2 ≤ c₁ := by
      rw [abs_of_nonneg (by omega)] at hsep
      omega
    have hcR : (c₂ : ℝ) + 2 ≤ (c₁ : ℝ) := by exact_mod_cast hc
    linarith
  · have hc : c₁ + 2 ≤ c₂ := by
      rw [abs_of_neg (by omega)] at hsep
      omega
    have hcR : (c₁ : ℝ) + 2 ≤ (c₂ : ℝ) := by exact_mod_cast hc
    linarith

/-- Exact cylinder characterization: `scaledCantorCoord α` lies in `cantorOpenInterval w` if and
only if `α` agrees with `w` on its first `m` entries. -/
theorem scaledCantorCoord_mem_cantorOpenInterval_iff {N m : ℕ} (α : ℕ → Fin N)
    (w : Fin m → Fin N) :
    scaledCantorCoord α ∈ cantorOpenInterval w ↔ ∀ j : Fin m, α j.1 = w j := by
  let wα : Fin m → Fin N := fun j ↦ α j.1
  have hmem_self : scaledCantorCoord α ∈ cantorOpenInterval wα := by
    unfold cantorOpenInterval scaledCantorCoord
    have hB : 0 < (cantorBase N : ℝ) ^ m := by
      have := cantorBase_pos N
      positivity
    have hden : 0 < (4 : ℝ) * (cantorBase N : ℝ) ^ m := by positivity
    have hlo := prefix_div_le_cantorCoord α m
    have hhi := cantorCoord_le_prefix_add_one_div α m
    constructor
    · rw [div_lt_iff₀ hden]
      have := (div_le_iff₀ hB).mp hlo
      linarith
    · rw [lt_div_iff₀ hden]
      have := (le_div_iff₀ hB).mp hhi
      linarith
  constructor
  · intro hx j
    by_contra hj
    have hne : wα ≠ w := fun heq ↦ hj (congrFun heq j)
    exact Set.disjoint_left.mp (disjoint_cantorOpenInterval hne) hmem_self hx
  · intro h
    have heq : wα = w := funext h
    rwa [← heq]

/-- `scaledCantorCoord` is injective on `ℕ → Fin N`. -/
theorem scaledCantorCoord_injective {N : ℕ} : Function.Injective (@scaledCantorCoord N) := by
  intro α β h
  funext i
  let w : Fin (i + 1) → Fin N := fun j ↦ α j.1
  have hα : scaledCantorCoord α ∈ cantorOpenInterval w :=
    (scaledCantorCoord_mem_cantorOpenInterval_iff α w).mpr fun _ ↦ rfl
  rw [h] at hα
  have hβ := (scaledCantorCoord_mem_cantorOpenInterval_iff β w).mp hα (Fin.last i)
  simpa [w] using hβ.symm

/-- Negative half-sequence `j ↦ s (-(j + 1))` of `s : ℤ → A`. -/
def negHalf {A : Type*} (s : ℤ → A) : ℕ → A :=
  fun j ↦ s (-((j : ℤ) + 1))

/-- Non-negative half-sequence `j ↦ s j` of `s : ℤ → A`. -/
def nonnegHalf {A : Type*} (s : ℤ → A) : ℕ → A :=
  fun j ↦ s (j : ℤ)

theorem continuous_negHalf {A : Type*} [TopologicalSpace A] :
    Continuous (@negHalf A) :=
  continuous_pi fun j ↦ continuous_apply (-((j : ℤ) + 1))

theorem continuous_nonnegHalf {A : Type*} [TopologicalSpace A] :
    Continuous (@nonnegHalf A) :=
  continuous_pi fun j ↦ continuous_apply (j : ℤ)

/-- Every point `(y₀, y₁)` in `(-1/2, 1/2) × (-1/2, 1/2)` lies strictly inside `UnitDisk2`
(`Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1`). -/
theorem toLp_mem_unitDisk2_of_mem_Ioo {y₀ y₁ : ℝ}
    (hy₀ : y₀ ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))
    (hy₁ : y₁ ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    WithLp.toLp 2 ![y₀, y₁] ∈ UnitDisk2 := by
  rw [UnitDisk2, Metric.mem_ball, dist_zero_right, EuclideanSpace.norm_eq]
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Real.norm_eq_abs,
    sq_abs]
  have h0 : y₀ ^ 2 < 1 / 4 := by nlinarith [hy₀.1, hy₀.2]
  have h1 : y₁ ^ 2 < 1 / 4 := by nlinarith [hy₁.1, hy₁.2]
  calc
    Real.sqrt (y₀ ^ 2 + y₁ ^ 2) < Real.sqrt 1 :=
      Real.sqrt_lt_sqrt (by positivity) (by linarith)
    _ = 1 := Real.sqrt_one

/-- Square middle-Cantor embedding `(ℤ → A) → UnitDisk2` associated to an alphabet numbering
`enc : A ≃ Fin N` (`Moore 1990`, `CMPP21` Equation 7). -/
noncomputable def cantorDiskEmbed {A : Type*} {N : ℕ} (enc : A ≃ Fin N) (s : ℤ → A) :
    UnitDisk2 :=
  ⟨WithLp.toLp 2
      ![scaledCantorCoord (fun j ↦ enc (negHalf s j)),
        scaledCantorCoord (fun j ↦ enc (nonnegHalf s j))],
    toLp_mem_unitDisk2_of_mem_Ioo
      (by
        have h := scaledCantorCoord_mem_Icc (fun j ↦ enc (negHalf s j))
        exact ⟨by linarith [h.1], by linarith [h.2]⟩)
      (by
        have h := scaledCantorCoord_mem_Icc (fun j ↦ enc (nonnegHalf s j))
        exact ⟨by linarith [h.1], by linarith [h.2]⟩)⟩

/-- `cantorDiskEmbed enc` is injective on `ℤ → A`. -/
theorem cantorDiskEmbed_injective {A : Type*} {N : ℕ} (enc : A ≃ Fin N) :
    Function.Injective (cantorDiskEmbed enc) := by
  intro s₁ s₂ h
  have hval := congrArg Subtype.val h
  have h0 : scaledCantorCoord (fun j ↦ enc (negHalf s₁ j)) =
      scaledCantorCoord (fun j ↦ enc (negHalf s₂ j)) :=
    congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) hval
  have h1 : scaledCantorCoord (fun j ↦ enc (nonnegHalf s₁ j)) =
      scaledCantorCoord (fun j ↦ enc (nonnegHalf s₂ j)) :=
    congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1) hval
  have hneg := scaledCantorCoord_injective h0
  have hpos := scaledCantorCoord_injective h1
  funext i
  rcases le_or_gt 0 i with hi | hi
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    exact enc.injective (congrFun hpos j)
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, i = -((j : ℤ) + 1) := ⟨(-i - 1).toNat, by omega⟩
    subst hj
    exact enc.injective (congrFun hneg j)

/-- `cantorDiskEmbed enc` is continuous from the product topology on `ℤ → A` (with discrete `A`)
into `UnitDisk2`. -/
theorem continuous_cantorDiskEmbed {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    {N : ℕ} (enc : A ≃ Fin N) : Continuous (cantorDiskEmbed enc) := by
  refine Continuous.subtype_mk ?_ _
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦ ?_)
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    refine continuous_scaledCantorCoord.comp (continuous_pi fun j ↦ ?_)
    exact (continuous_of_discreteTopology (f := ⇑enc)).comp
      ((continuous_apply j).comp continuous_negHalf)
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    refine continuous_scaledCantorCoord.comp (continuous_pi fun j ↦ ?_)
    exact (continuous_of_discreteTopology (f := ⇑enc)).comp
      ((continuous_apply j).comp continuous_nonnegHalf)

/-- Extract the negative-side prefix `Fin k → Fin N` (`-1, …, -k`) from a window on `[-k, k]`. -/
def windowNegPrefix {A : Type*} {N : ℕ} (enc : A ≃ Fin N) (k : ℕ)
    (w : Set.Icc (-(k : ℤ)) (k : ℤ) → A) : Fin k → Fin N :=
  fun j ↦ enc (w ⟨-((j.1 : ℤ) + 1), ⟨by omega, by omega⟩⟩)

/-- Extract the non-negative-side prefix `Fin (k + 1) → Fin N` (`0, …, k`) from a window on
`[-k, k]`. -/
def windowNonnegPrefix {A : Type*} {N : ℕ} (enc : A ≃ Fin N) (k : ℕ)
    (w : Set.Icc (-(k : ℤ)) (k : ℤ) → A) : Fin (k + 1) → Fin N :=
  fun j ↦ enc (w ⟨(j.1 : ℤ), ⟨by omega, by omega⟩⟩)

/-- Nonempty open rectangle inside `UnitDisk2` associated to a finite cylinder block
`w : Set.Icc (-k) k → A`. -/
noncomputable def cantorCylinderRect {A : Type*} {N : ℕ} (enc : A ≃ Fin N) (k : ℕ)
    (w : Set.Icc (-(k : ℤ)) (k : ℤ) → A) : Opens UnitDisk2 :=
  ⟨((fun y : UnitDisk2 ↦ y.1 0) ⁻¹' cantorOpenInterval (windowNegPrefix enc k w)) ∩
      ((fun y : UnitDisk2 ↦ y.1 1) ⁻¹' cantorOpenInterval (windowNonnegPrefix enc k w)),
    ((isOpen_cantorOpenInterval _).preimage
        ((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).comp continuous_subtype_val)).inter
      ((isOpen_cantorOpenInterval _).preimage
        ((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1).comp continuous_subtype_val))⟩

theorem mem_cantorCylinderRect_iff {A : Type*} {N : ℕ} (enc : A ≃ Fin N) (k : ℕ)
    (w : Set.Icc (-(k : ℤ)) (k : ℤ) → A) (y : UnitDisk2) :
    y ∈ cantorCylinderRect enc k w ↔
      y.1 0 ∈ cantorOpenInterval (windowNegPrefix enc k w) ∧
      y.1 1 ∈ cantorOpenInterval (windowNonnegPrefix enc k w) :=
  Iff.rfl

/-- Every cylinder rectangle `cantorCylinderRect enc k w` is nonempty inside `UnitDisk2`. -/
theorem cantorCylinderRect_nonempty {A : Type*} {N : ℕ} (enc : A ≃ Fin N) (k : ℕ)
    (w : Set.Icc (-(k : ℤ)) (k : ℤ) → A) :
    (cantorCylinderRect enc k w : Set UnitDisk2).Nonempty := by
  obtain ⟨y₀, hy₀⟩ := cantorOpenInterval_nonempty (windowNegPrefix enc k w)
  obtain ⟨y₁, hy₁⟩ := cantorOpenInterval_nonempty (windowNonnegPrefix enc k w)
  refine ⟨⟨WithLp.toLp 2 ![y₀, y₁],
    toLp_mem_unitDisk2_of_mem_Ioo
      (cantorOpenInterval_subset_Ioo_half _ hy₀)
      (cantorOpenInterval_subset_Ioo_half _ hy₁)⟩, ?_⟩
  exact ⟨hy₀, hy₁⟩

/-- Distinct cylinder windows on `[-k, k]` map to pairwise disjoint open rectangles in
`UnitDisk2`. -/
theorem disjoint_cantorCylinderRect {A : Type*} {N : ℕ} (enc : A ≃ Fin N) (k : ℕ)
    {w₁ w₂ : Set.Icc (-(k : ℤ)) (k : ℤ) → A} (hne : w₁ ≠ w₂) :
    Disjoint (cantorCylinderRect enc k w₁ : Set UnitDisk2)
      (cantorCylinderRect enc k w₂ : Set UnitDisk2) := by
  rw [Set.disjoint_iff]
  rintro y ⟨h1, h2⟩
  rcases h1 with ⟨h10, h11⟩
  rcases h2 with ⟨h20, h21⟩
  by_cases hneg : windowNegPrefix enc k w₁ = windowNegPrefix enc k w₂
  · have hpos_ne : windowNonnegPrefix enc k w₁ ≠ windowNonnegPrefix enc k w₂ := by
      intro hpos
      apply hne
      funext ⟨i, hi⟩
      obtain ⟨hi1, hi2⟩ := hi
      rcases le_or_gt 0 i with h0 | h0
      · obtain ⟨m_i, rfl⟩ := Int.eq_ofNat_of_zero_le h0
        let j : Fin (k + 1) := ⟨m_i, by omega⟩
        exact enc.injective (congrFun hpos j)
      · obtain ⟨m_i, rfl⟩ : ∃ m_i : ℕ, i = -((m_i : ℤ) + 1) := ⟨(-i - 1).toNat, by omega⟩
        let j : Fin k := ⟨m_i, by omega⟩
        exact enc.injective (congrFun hneg j)
    exact Set.disjoint_left.mp (disjoint_cantorOpenInterval hpos_ne) h11 h21
  · exact Set.disjoint_left.mp (disjoint_cantorOpenInterval hneg) h10 h20

/-- Exact Cantor-rectangle preimage property: `cantorDiskEmbed enc s` belongs to
`cantorCylinderRect enc k w` if and only if `s ∈ cylinderIcc k w`. -/
theorem cantorDiskEmbed_mem_cantorCylinderRect_iff {A : Type*} {N : ℕ} (enc : A ≃ Fin N)
    (s : ℤ → A) (k : ℕ) (w : Set.Icc (-(k : ℤ)) (k : ℤ) → A) :
    cantorDiskEmbed enc s ∈ cantorCylinderRect enc k w ↔ s ∈ cylinderIcc k w := by
  rw [mem_cantorCylinderRect_iff]
  have hc0 : (cantorDiskEmbed enc s).1 0 = scaledCantorCoord (fun j ↦ enc (negHalf s j)) := rfl
  have hc1 : (cantorDiskEmbed enc s).1 1 = scaledCantorCoord (fun j ↦ enc (nonnegHalf s j)) := rfl
  rw [hc0, hc1, scaledCantorCoord_mem_cantorOpenInterval_iff,
    scaledCantorCoord_mem_cantorOpenInterval_iff]
  constructor
  · rintro ⟨hneg, hpos⟩ ⟨i, hi⟩
    obtain ⟨hi1, hi2⟩ := hi
    rcases le_or_gt 0 i with h0 | h0
    · obtain ⟨m_i, rfl⟩ := Int.eq_ofNat_of_zero_le h0
      let j : Fin (k + 1) := ⟨m_i, by omega⟩
      exact enc.injective (hpos j)
    · obtain ⟨m_i, rfl⟩ : ∃ m_i : ℕ, i = -((m_i : ℤ) + 1) := ⟨(-i - 1).toNat, by omega⟩
      let j : Fin k := ⟨m_i, by omega⟩
      exact enc.injective (hneg j)
  · intro hs
    refine ⟨fun j ↦ ?_, fun j ↦ ?_⟩
    · simp only [negHalf, windowNegPrefix]
      exact congrArg enc (hs ⟨-((j.1 : ℤ) + 1), ⟨by omega, by omega⟩⟩)
    · simp only [nonnegHalf, windowNonnegPrefix]
      exact congrArg enc (hs ⟨(j.1 : ℤ), ⟨by omega, by omega⟩⟩)

/-! ### Computable `2⁻ᵐ` Dyadic/Cantor Rational Approximations (`RatFrac × RatFrac`) -/

/-- Iterative `(numerator, B^len)` accumulator over a list of digits `[d_0, …, d_{len-1}]`. -/
def cantorPrefixPairList (B : ℕ) (digits : List ℕ) : ℕ × ℕ :=
  digits.foldl (fun acc d ↦ (B * acc.1 + 2 * d, B * acc.2)) (0, 1)

theorem cantorPrefixPairList_snd (B : ℕ) (digits : List ℕ) :
    (cantorPrefixPairList B digits).2 = B ^ digits.length := by
  unfold cantorPrefixPairList
  have hgen : ∀ (l : List ℕ) (a p : ℕ),
      (l.foldl (fun acc d ↦ (B * acc.1 + 2 * d, B * acc.2)) (a, p)).2 = p * B ^ l.length := by
    intro l
    induction l with
    | nil => simp
    | cons d l ih =>
      intro a p
      simp only [List.foldl_cons, List.length_cons, ih, pow_succ]
      ring
  simpa using hgen digits 0 1

theorem cantorPrefixPairList_range_fst (B : ℕ) (f : ℕ → ℕ) :
    ∀ m : ℕ,
      (cantorPrefixPairList B ((List.range m).map f)).1 =
        cantorPrefixCode B (fun j : Fin m ↦ f j.1)
  | 0 => rfl
  | m + 1 => by
    unfold cantorPrefixPairList at *
    rw [List.range_succ, List.map_append, List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, cantorPrefixCode,
      Fin.val_last, Fin.val_castSucc]
    congr 2
    exact cantorPrefixPairList_range_fst B f m

/-- Build a non-negative `RatFrac` representing `num / (4 * den)` for `den ≥ 1`. -/
def mkPosQuarterRatFrac (num den : ℕ) : RatFrac :=
  (false, num, 4 * den - 1)

theorem mkPosQuarterRatFrac_toReal (num : ℕ) {den : ℕ} (hden : 1 ≤ den) :
    (mkPosQuarterRatFrac num den).toReal = (num : ℝ) / (4 * (den : ℝ)) := by
  unfold mkPosQuarterRatFrac RatFrac.toReal RatFrac.toRat
  simp only [Bool.false_eq_true, ↓reduceIte, Rat.cast_div, Rat.cast_natCast, Rat.cast_add,
    Rat.cast_one]
  congr 1
  have h4 : 1 ≤ 4 * den := by omega
  exact_mod_cast Nat.sub_add_cancel h4

/-- Primitive-recursive rational approximation of `scaledCantorCoord α` using the first `m + 1`
digits `[α 0, …, α m]`. -/
def approxCantorList (B : ℕ) (digits : List ℕ) : RatFrac :=
  let p := cantorPrefixPairList B digits
  mkPosQuarterRatFrac p.1 p.2

theorem primrec_cantorPrefixPairList (B : ℕ) : Primrec (cantorPrefixPairList B) := by
  have hacc1 : Primrec (fun x : List ℕ × (ℕ × ℕ) × ℕ ↦ x.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hacc2 : Primrec (fun x : List ℕ × (ℕ × ℕ) × ℕ ↦ x.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hd : Primrec (fun x : List ℕ × (ℕ × ℕ) × ℕ ↦ x.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hstep : Primrec₂ (fun (_ : List ℕ) (ad : (ℕ × ℕ) × ℕ) ↦
      (B * ad.1.1 + 2 * ad.2, B * ad.1.2)) :=
    (Primrec.pair
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const B) hacc1)
        (Primrec.nat_mul.comp (Primrec.const 2) hd))
      (Primrec.nat_mul.comp (Primrec.const B) hacc2)).to₂
  exact (Primrec.list_foldl (f := id) Primrec.id (Primrec.const (0, 1)) hstep).of_eq fun _ ↦ rfl

theorem primrec_approxCantorList (B : ℕ) : Primrec (approxCantorList B) := by
  unfold approxCantorList mkPosQuarterRatFrac
  have hp := primrec_cantorPrefixPairList B
  exact Primrec.pair (Primrec.const false)
    (Primrec.pair (Primrec.fst.comp hp)
      (Primrec.nat_sub.comp
        (Primrec.nat_mul.comp (Primrec.const 4) (Primrec.snd.comp hp))
        (Primrec.const 1)))

theorem abs_approxCantorList_sub_scaledCantorCoord {N : ℕ} (α : ℕ → Fin N) (m : ℕ) :
    |(approxCantorList (cantorBase N) ((List.range (m + 1)).map fun j ↦ (α j).1)).toReal -
        scaledCantorCoord α| ≤
      1 / (4 * (cantorBase N : ℝ) ^ (m + 1)) := by
  have hBpos : 1 ≤ (cantorBase N) ^ (m + 1) :=
    Nat.one_le_pow (m + 1) _ (le_trans (by decide : 1 ≤ 3) (three_le_cantorBase N))
  have hlen : ((List.range (m + 1)).map fun j ↦ (α j).1).length = m + 1 := by simp
  have hsnd : (cantorPrefixPairList (cantorBase N) ((List.range (m + 1)).map fun j ↦ (α j).1)).2 =
      (cantorBase N) ^ (m + 1) := by
    rw [cantorPrefixPairList_snd, hlen]
  have hfst := cantorPrefixPairList_range_fst (cantorBase N) (fun j ↦ (α j).1) (m + 1)
  have hreal :
      (approxCantorList (cantorBase N) ((List.range (m + 1)).map fun j ↦ (α j).1)).toReal =
        (cantorPrefixCode (cantorBase N) (fun j : Fin (m + 1) ↦ (α j.1).1) : ℝ) /
          (4 * (cantorBase N : ℝ) ^ (m + 1)) := by
    unfold approxCantorList
    rw [mkPosQuarterRatFrac_toReal _ (by rw [hsnd]; exact hBpos), hfst, hsnd]
    push_cast
    rfl
  rw [hreal]
  have hlo := prefix_div_le_cantorCoord α (m + 1)
  have hhi := cantorCoord_le_prefix_add_one_div α (m + 1)
  unfold scaledCantorCoord
  set K : ℝ := (cantorPrefixCode (cantorBase N) (fun j : Fin (m + 1) ↦ (α j.1).1) : ℝ)
  set BM : ℝ := (cantorBase N : ℝ) ^ (m + 1)
  have hBM : 0 < BM := by
    have := cantorBase_pos N
    positivity
  have h1 : K / (4 * BM) ≤ (1 / 4 : ℝ) * cantorCoord α := by
    have : K / (4 * BM) = (1 / 4 : ℝ) * (K / BM) := by ring
    linarith
  have h2 : (1 / 4 : ℝ) * cantorCoord α ≤ K / (4 * BM) + 1 / (4 * BM) := by
    have : K / (4 * BM) + 1 / (4 * BM) = (1 / 4 : ℝ) * ((K + 1) / BM) := by ring
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- Explicit equivalence `Option (Option Λ) ≃ Fin (nΛ + 2)` mapping `none ↦ 0`,
`some none ↦ 1`, and `some (some q) ↦ 2 + encΛ q`. -/
def optionOptionEquivFin {Λ : Type*} {nΛ : ℕ} (encΛ : Λ ≃ Fin nΛ) :
    Option (Option Λ) ≃ Fin (nΛ + 2) where
  toFun
    | none => ⟨0, by omega⟩
    | some none => ⟨1, by omega⟩
    | some (some q) => ⟨(encΛ q).1 + 2, by have := (encΛ q).2; omega⟩
  invFun i :=
    if h0 : i.1 = 0 then none
    else if h1 : i.1 = 1 then some none
    else some (some (encΛ.symm ⟨i.1 - 2, by have := i.2; omega⟩))
  left_inv x := by
    rcases x with _ | (_ | q)
    · simp
    · simp
    · have h0 : (encΛ q).1 + 2 ≠ 0 := by omega
      have h1 : (encΛ q).1 + 2 ≠ 1 := by omega
      simp [h1]
  right_inv i := by
    rcases i with ⟨v, hv⟩
    by_cases h0 : v = 0
    · subst h0; rfl
    · by_cases h1 : v = 1
      · subst h1; rfl
      · simp only [h0, h1, ↓reduceDIte, Fin.mk.injEq]
        have heq : (encΛ (encΛ.symm ⟨v - 2, by omega⟩)).1 = v - 2 := by
          rw [Equiv.apply_symm_apply]
        omega

/-- Explicit equivalence `M.ShiftAlphabet ≃ Fin (Fintype.card M.ShiftAlphabet)` with transparent
arithmetic formula `(encΓ a).1 * (card Λ + 2) + code(o)` for computable rational approximations. -/
def shiftAlphabetEquivFin (M : FinTM0)
    (encΓ : M.Γ ≃ Fin (Fintype.card M.Γ)) (encΛ : M.Λ ≃ Fin (Fintype.card M.Λ)) :
    M.ShiftAlphabet ≃ Fin (Fintype.card M.ShiftAlphabet) :=
  ((Equiv.prodCongr encΓ (optionOptionEquivFin encΛ)).trans finProdFinEquiv).trans
    (finCongr (by simp [FinTM0.ShiftAlphabet, Fintype.card_prod, Fintype.card_option]))

@[simp]
theorem shiftAlphabetEquivFin_val_none (M : FinTM0)
    (encΓ : M.Γ ≃ Fin (Fintype.card M.Γ)) (encΛ : M.Λ ≃ Fin (Fintype.card M.Λ)) (a : M.Γ) :
    (shiftAlphabetEquivFin M encΓ encΛ (a, none)).1 =
      (encΓ a).1 * (Fintype.card M.Λ + 2) := by
  simp [shiftAlphabetEquivFin, optionOptionEquivFin, finProdFinEquiv]
  ring

@[simp]
theorem shiftAlphabetEquivFin_val_some_some (M : FinTM0)
    (encΓ : M.Γ ≃ Fin (Fintype.card M.Γ)) (encΛ : M.Λ ≃ Fin (Fintype.card M.Λ))
    (a : M.Γ) (q : M.Λ) :
    (shiftAlphabetEquivFin M encΓ encΛ (a, some (some q))).1 =
      (encΓ a).1 * (Fintype.card M.Λ + 2) + ((encΛ q).1 + 2) := by
  simp [shiftAlphabetEquivFin, optionOptionEquivFin, finProdFinEquiv]
  ring

/-- Computable `2⁻ᵐ` `RatFrac × RatFrac` chart approximations for
`cantorDiskEmbed (shiftAlphabetEquivFin M encΓ encΛ) (M.encodeInit (Turing.Tape.mk₂ L R))`
matching `TuringCompleteWitness.computable_approx` (`Interfaces.lean`). -/
theorem FinTM0.exists_computable_approx_cantorDiskEmbed (M : FinTM0) :
    let encΓ := Fintype.equivFin M.Γ
    let encΛ := Fintype.equivFin M.Λ
    let encS := shiftAlphabetEquivFin M encΓ encΛ
    ∃ approx :
        List (Fin (Fintype.card M.Γ)) × List (Fin (Fintype.card M.Γ)) × ℕ →
          RatFrac × RatFrac,
      Computable approx ∧
      ∀ (L R : List M.Γ) (m : ℕ),
        ‖ratFracPairToEuclidean2 (approx (L.map encΓ, R.map encΓ, m)) -
            (cantorDiskEmbed encS (M.encodeInit (Turing.Tape.mk₂ L R))).1‖ ≤
          (1 / 2 : ℝ) ^ m := by
  intro encΓ encΛ encS
  let N := Fintype.card M.ShiftAlphabet
  let B := cantorBase N
  let d₀ : Fin (Fintype.card M.Γ) := encΓ default
  let q₀ : ℕ := (encΛ default).1
  let stride : ℕ := Fintype.card M.Λ + 2
  let negDigits : List (Fin (Fintype.card M.Γ)) × List (Fin (Fintype.card M.Γ)) × ℕ → List ℕ :=
    fun p ↦ (List.range (p.2.2 + 1)).map fun j ↦ (p.1.getD j d₀).1 * stride
  let posDigits : List (Fin (Fintype.card M.Γ)) × List (Fin (Fintype.card M.Γ)) × ℕ → List ℕ :=
    fun p ↦ (List.range (p.2.2 + 1)).map fun j ↦
      if j = 0 then (p.2.1.getD 0 d₀).1 * stride + (q₀ + 2)
      else (p.2.1.tail.getD (j - 1) d₀).1 * stride
  let approx : List (Fin (Fintype.card M.Γ)) × List (Fin (Fintype.card M.Γ)) × ℕ →
      RatFrac × RatFrac :=
    fun p ↦ (approxCantorList B (negDigits p), approxCantorList B (posDigits p))
  refine ⟨approx, ?_, ?_⟩
  · apply Primrec.to_comp
    have hL : Primrec (fun p : List (Fin (Fintype.card M.Γ)) ×
        List (Fin (Fintype.card M.Γ)) × ℕ ↦ p.1) := Primrec.fst
    have hR : Primrec (fun p : List (Fin (Fintype.card M.Γ)) ×
        List (Fin (Fintype.card M.Γ)) × ℕ ↦ p.2.1) := Primrec.fst.comp Primrec.snd
    have hm : Primrec (fun p : List (Fin (Fintype.card M.Γ)) ×
        List (Fin (Fintype.card M.Γ)) × ℕ ↦ p.2.2) := Primrec.snd.comp Primrec.snd
    have hrange : Primrec (fun p : List (Fin (Fintype.card M.Γ)) ×
        List (Fin (Fintype.card M.Γ)) × ℕ ↦ List.range (p.2.2 + 1)) :=
      Primrec.list_range.comp (Primrec.succ.comp hm)
    have hneg : Primrec negDigits := by
      have hget : Primrec (fun q : (List (Fin (Fintype.card M.Γ)) ×
          List (Fin (Fintype.card M.Γ)) × ℕ) × ℕ ↦ q.1.1.getD q.2 d₀) :=
        (Primrec.list_getD d₀).comp (hL.comp Primrec.fst) Primrec.snd
      have hbody : Primrec₂ (fun (p : List (Fin (Fintype.card M.Γ)) ×
          List (Fin (Fintype.card M.Γ)) × ℕ) (j : ℕ) ↦ (p.1.getD j d₀).1 * stride) :=
        (Primrec.nat_mul.comp (Primrec.fin_val.comp hget) (Primrec.const stride)).to₂
      exact Primrec.list_map hrange hbody
    have hpos : Primrec posDigits := by
      have hzero : Primrec (fun q : (List (Fin (Fintype.card M.Γ)) ×
          List (Fin (Fintype.card M.Γ)) × ℕ) × ℕ ↦
            (q.1.2.1.getD 0 d₀).1 * stride + (q₀ + 2)) :=
        Primrec.nat_add.comp
          (Primrec.nat_mul.comp
            (Primrec.fin_val.comp ((Primrec.list_getD d₀).comp (hR.comp Primrec.fst)
              (Primrec.const 0)))
            (Primrec.const stride))
          (Primrec.const (q₀ + 2))
      have helse : Primrec (fun q : (List (Fin (Fintype.card M.Γ)) ×
          List (Fin (Fintype.card M.Γ)) × ℕ) × ℕ ↦
            (q.1.2.1.tail.getD (q.2 - 1) d₀).1 * stride) :=
        Primrec.nat_mul.comp
          (Primrec.fin_val.comp
            ((Primrec.list_getD d₀).comp
              (Primrec.list_tail.comp (hR.comp Primrec.fst))
              (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1))))
          (Primrec.const stride)
      have hcond : PrimrecPred (fun q : (List (Fin (Fintype.card M.Γ)) ×
          List (Fin (Fintype.card M.Γ)) × ℕ) × ℕ ↦ q.2 = 0) :=
        Primrec.eq.comp Primrec.snd (Primrec.const 0)
      exact Primrec.list_map hrange (Primrec.ite hcond hzero helse).to₂
    exact Primrec.pair ((primrec_approxCantorList B).comp hneg)
      ((primrec_approxCantorList B).comp hpos)
  · intro L R m
    let s := M.encodeInit (Turing.Tape.mk₂ L R)
    have hneg_eq :
        negDigits (L.map encΓ, R.map encΓ, m) =
          (List.range (m + 1)).map fun j ↦ (encS (negHalf s j)).1 := by
      refine List.map_congr_left fun j _ ↦ ?_
      have hnth : (Turing.Tape.mk₂ L R).nth (-((j : ℤ) + 1)) = L.getI j := rfl
      have hget : (L.map encΓ).getD j d₀ = encΓ (L.getI j) := by
        rw [← List.getD_default_eq_getI, List.getD_map]
      have hite : (if -((j : ℤ) + 1) = 0 then some (some (default : M.Λ)) else none) = none :=
        ite_eq_right_iff.mpr fun h ↦ by omega
      dsimp only [s, FinTM0.encodeInit, FinTM0.encodeActiveCfg, FinTM0.initCfg, negHalf, encS,
        stride]
      rw [hite, hnth, hget, shiftAlphabetEquivFin_val_none]
    have hpos_eq :
        posDigits (L.map encΓ, R.map encΓ, m) =
          (List.range (m + 1)).map fun j ↦ (encS (nonnegHalf s j)).1 := by
      refine List.map_congr_left fun j _ ↦ ?_
      rcases j with _ | i
      · have hnth0 : (Turing.Tape.mk₂ L R).nth 0 = R.headI := rfl
        have hget0 : (R.map encΓ).getD 0 d₀ = encΓ R.headI := by
          rcases R with _ | ⟨a, rs⟩ <;> rfl
        have h0 : s 0 = (R.headI, some (some default)) := by
          simp [s, FinTM0.encodeInit, FinTM0.encodeActiveCfg, FinTM0.initCfg, hnth0]
        change (if (0 : ℕ) = 0 then ((R.map encΓ).getD 0 d₀).1 * stride + (q₀ + 2) else _) =
          (encS (s 0)).1
        rw [h0, hget0]
        exact (shiftAlphabetEquivFin_val_some_some M encΓ encΛ R.headI default).symm
      · have hnthS : (Turing.Tape.mk₂ L R).nth ((i : ℤ) + 1) = R.tail.getI i := rfl
        have hgetS : (R.map encΓ).tail.getD i d₀ = encΓ (R.tail.getI i) := by
          rw [← List.map_tail, ← List.getD_default_eq_getI, List.getD_map]
        have hsS : s ((i + 1 : ℕ) : ℤ) = (R.tail.getI i, none) := by
          have hne0 : ((i + 1 : ℕ) : ℤ) ≠ 0 := by omega
          have hcast : (((i + 1 : ℕ) : ℤ)) = (i : ℤ) + 1 := by push_cast; rfl
          dsimp only [s, FinTM0.encodeInit, FinTM0.encodeActiveCfg, FinTM0.initCfg]
          rw [ite_eq_right_iff.mpr (fun h ↦ (hne0 h).elim), hcast, hnthS]
        change (if i + 1 = 0 then _ else ((R.map encΓ).tail.getD i d₀).1 * stride) =
          (encS (s ((i + 1 : ℕ) : ℤ))).1
        have hne_nat : i + 1 ≠ 0 := Nat.succ_ne_zero i
        rw [ite_eq_right_iff.mpr (fun h ↦ (hne_nat h).elim), hsS, hgetS]
        exact (shiftAlphabetEquivFin_val_none M encΓ encΛ (R.tail.getI i)).symm
    have herr0 :
        |(approx (L.map encΓ, R.map encΓ, m)).1.toReal -
            scaledCantorCoord (fun j ↦ encS (negHalf s j))| ≤
          1 / (4 * (B : ℝ) ^ (m + 1)) := by
      dsimp [approx]
      rw [hneg_eq]
      exact abs_approxCantorList_sub_scaledCantorCoord (fun j ↦ encS (negHalf s j)) m
    have herr1 :
        |(approx (L.map encΓ, R.map encΓ, m)).2.toReal -
            scaledCantorCoord (fun j ↦ encS (nonnegHalf s j))| ≤
          1 / (4 * (B : ℝ) ^ (m + 1)) := by
      dsimp [approx]
      rw [hpos_eq]
      exact abs_approxCantorList_sub_scaledCantorCoord (fun j ↦ encS (nonnegHalf s j)) m
    set e₀ : ℝ := (approx (L.map encΓ, R.map encΓ, m)).1.toReal -
        scaledCantorCoord (fun j ↦ encS (negHalf s j))
    set e₁ : ℝ := (approx (L.map encΓ, R.map encΓ, m)).2.toReal -
        scaledCantorCoord (fun j ↦ encS (nonnegHalf s j))
    have hnorm :
        ‖ratFracPairToEuclidean2 (approx (L.map encΓ, R.map encΓ, m)) -
            (cantorDiskEmbed encS s).1‖ = Real.sqrt (e₀ ^ 2 + e₁ ^ 2) := by
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
      simp only [ratFracPairToEuclidean2, cantorDiskEmbed, PiLp.sub_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs, e₀, e₁]
    rw [hnorm]
    have h2pos : 0 < (2 : ℝ) ^ (m + 1) := by positivity
    have hB2 : (2 : ℝ) ^ (m + 1) ≤ (B : ℝ) ^ (m + 1) := by
      refine pow_le_pow_left₀ (by positivity) ?_ (m + 1)
      exact_mod_cast le_trans (by decide : 2 ≤ 3) (three_le_cantorBase N)
    have hbound : 1 / (4 * (B : ℝ) ^ (m + 1)) ≤ (1 / 2 : ℝ) ^ (m + 1) := by
      rw [one_div_pow]
      have h4 : (2 : ℝ) ^ (m + 1) ≤ 4 * (B : ℝ) ^ (m + 1) := by linarith
      exact one_div_le_one_div_of_le h2pos h4
    have he0 : |e₀| ≤ (1 / 2 : ℝ) ^ (m + 1) := herr0.trans hbound
    have he1 : |e₁| ≤ (1 / 2 : ℝ) ^ (m + 1) := herr1.trans hbound
    have hsq0 : e₀ ^ 2 ≤ ((1 / 2 : ℝ) ^ (m + 1)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) he0 2
    have hsq1 : e₁ ^ 2 ≤ ((1 / 2 : ℝ) ^ (m + 1)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) he1 2
    have hsum_sq : e₀ ^ 2 + e₁ ^ 2 ≤ ((1 / 2 : ℝ) ^ m) ^ 2 := by
      have hhalf : ((1 / 2 : ℝ) ^ (m + 1)) ^ 2 + ((1 / 2 : ℝ) ^ (m + 1)) ^ 2 =
          (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ m) ^ 2 := by
        rw [pow_succ]
        ring
      have hpos_m : 0 ≤ ((1 / 2 : ℝ) ^ m) ^ 2 := sq_nonneg _
      linarith
    calc
      Real.sqrt (e₀ ^ 2 + e₁ ^ 2) ≤ Real.sqrt (((1 / 2 : ℝ) ^ m) ^ 2) :=
        Real.sqrt_le_sqrt hsum_sq
      _ = (1 / 2 : ℝ) ^ m := Real.sqrt_sq (by positivity)

end S4TuringPoisson
