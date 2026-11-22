-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.AxisRect.ofCenter_xMax, tier: T0, attempt: 1, spec: Primitives.lean)
@[simp]
theorem AxisRect.ofCenter_xMax (c : EuclideanPlane) {δ₀ δ₁ : ℝ} (hδ₀ : 0 ≤ δ₀)
    (hδ₁ : 0 ≤ δ₁) :
    (AxisRect.ofCenter c hδ₀ hδ₁).xMax = c 0 + δ₀ :=
  by
  simp [AxisRect.ofCenter]
