-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.AxisRect.ofCenter_yMax, tier: T0, attempt: 2, spec: Primitives.lean)
@[simp]
theorem AxisRect.ofCenter_yMax (c : EuclideanPlane) {δ₀ δ₁ : ℝ} (hδ₀ : 0 ≤ δ₀)
    (hδ₁ : 0 ≤ δ₁) :
    (AxisRect.ofCenter c hδ₀ hδ₁).yMax = c 1 + δ₁ :=
  by
  simp [AxisRect.ofCenter]
