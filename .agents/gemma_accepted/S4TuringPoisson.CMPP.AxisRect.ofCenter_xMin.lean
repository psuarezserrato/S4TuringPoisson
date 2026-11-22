-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.AxisRect.ofCenter_xMin, tier: T0, attempt: 1, spec: Primitives.lean)
@[simp]
theorem AxisRect.ofCenter_xMin (c : EuclideanPlane) {δ₀ δ₁ : ℝ} (hδ₀ : 0 ≤ δ₀)
    (hδ₁ : 0 ≤ δ₁) :
    (AxisRect.ofCenter c hδ₀ hδ₁).xMin = c 0 - δ₀ :=
  by
  simp [AxisRect.ofCenter]
