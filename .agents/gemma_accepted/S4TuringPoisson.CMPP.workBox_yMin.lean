-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.workBox_yMin, tier: T0, attempt: 3, spec: Relocation.lean)
@[simp]
theorem workBox_yMin : workBox.yMin = -19 / 40 :=
  by
  unfold workBox
  norm_num
