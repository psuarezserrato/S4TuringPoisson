-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.biDirToyEnc_true_some_false, tier: T0, attempt: 2, spec: Realize.lean)
@[simp]
theorem biDirToyEnc_true_some_false : biDirToyEnc (true, some false) = 4 :=
  by
  unfold biDirToyEnc
  simp
