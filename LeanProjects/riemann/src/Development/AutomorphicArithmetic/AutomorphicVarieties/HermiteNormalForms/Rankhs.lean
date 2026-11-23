import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.rankhs :
    ∀ (L : Type) [Field L] [NumberField L] [IsTotallyComplex L] (N : ℕ), Module.finrank ℝ (HS L N) ≤ dd L N * N := by
  intro L _ _ _ N
  refine (Submodule.finrank_le (HSsub L N)).trans (le_of_eq ?_)
  have h1 := IsTotallyComplex.finrank L
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces L
  have h3 := IsTotallyComplex.nrRealPlaces_eq_zero L
  simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, dd]
  rw [h1, h2, h3]
  ring
