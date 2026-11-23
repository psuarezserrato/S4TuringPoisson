-- Verified by gemma_loop.py (declaration: S4TuringPoisson.composePoissonHamiltonianTimeOneFlows_nil, tier: T0, attempt: 1, spec: PoissonHamiltonian.lean)
@[simp]
theorem composePoissonHamiltonianTimeOneFlows_nil
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
    [A : AdmitsWrinkledOrBrokenLefschetzFibration M] :
    composePoissonHamiltonianTimeOneFlows M [] = Diffeomorph.refl (𝓡 4) M ∞ :=
  by
  rfl
