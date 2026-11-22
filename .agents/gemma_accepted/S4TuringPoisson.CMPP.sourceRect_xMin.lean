-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.sourceRect_xMin, tier: T0, attempt: 2, spec: Digits.lean)
@[simp]
theorem sourceRect_xMin {A : Type*} {N : ℕ} (enc : A ≃ Fin N) (w : shiftDom3 → A) :
    (sourceRect enc w).xMin = (2 * ((enc (w dom3NegOne)).1 : ℝ)) / (4 * (cantorBase N : ℝ)) :=
  by
  unfold sourceRect
  unfold AxisRect.xMin
  simp [dom3NegOne]
