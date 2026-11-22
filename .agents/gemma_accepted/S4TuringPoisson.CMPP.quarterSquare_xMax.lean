-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.quarterSquare_xMax, tier: T0, attempt: 2, spec: Digits.lean)
@[simp]
theorem quarterSquare_xMax : quarterSquare.xMax = 1 / 4 :=
  by
  unfold quarterSquare
  simp
