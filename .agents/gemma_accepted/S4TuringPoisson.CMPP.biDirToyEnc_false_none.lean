-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.biDirToyEnc_false_none, tier: T0, attempt: 4, spec: Realize.lean)
@[simp]
theorem biDirToyEnc_false_none : biDirToyEnc (false, none) = 0 :=
  by
  unfold biDirToyEnc
  simp
