-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.workBox_xMax, tier: T0, attempt: 2, spec: Relocation.lean)
@[simp]
theorem workBox_xMax : workBox.xMax = 11 / 20 :=
  by
  unfold workBox
  norm_num
