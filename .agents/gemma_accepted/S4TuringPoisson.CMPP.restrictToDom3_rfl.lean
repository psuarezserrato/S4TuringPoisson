-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.restrictToDom3_rfl, tier: T0, attempt: 1, spec: Realize.lean)
@[simp]
theorem restrictToDom3_rfl {A : Type*} (w : shiftDom3 → A) :
    restrictToDom3 rfl w = w :=
  by
  rfl
