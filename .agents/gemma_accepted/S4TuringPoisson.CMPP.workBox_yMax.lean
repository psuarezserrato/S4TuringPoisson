-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.workBox_yMax, tier: T0, attempt: 2, spec: Relocation.lean)
@[simp]
theorem workBox_yMax : workBox.yMax = 1 / 4 :=
  by
  unfold workBox
  norm_num
