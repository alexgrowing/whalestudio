import Mathlib

open IsLocalRing Polynomial

theorem UpperTheory.V.Th.Sp.dlam :
    ∀ (O σ : Type) [CommRing O] [DecidableEq σ] (th : MvPowerSeries σ O →ₐ[O] O) (k : σ), ∃ d : MvPowerSeries σ O →ₗ[O] O, (∀ a b, d (a * b) = th a • d b + th b • d a) ∧ ∀ k', d (MvPowerSeries.X k') = if k = k' then 1 else 0 := by
  intro O σ _ _ th k
  refine ⟨th.toLinearMap ∘ₗ (MvPowerSeries.pderiv O k).toLinearMap, ?_, ?_⟩
  · intro a b
    show th (MvPowerSeries.pderiv O k (a * b)) =
      th a • th (MvPowerSeries.pderiv O k b) + th b • th (MvPowerSeries.pderiv O k a)
    rw [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul, smul_eq_mul,
      smul_eq_mul]
  · intro k'
    show th (MvPowerSeries.pderiv O k (MvPowerSeries.X k')) = if k = k' then 1 else 0
    by_cases h : k = k'
    · subst h
      rw [MvPowerSeries.pderiv_X_self, map_one, if_pos rfl]
    · rw [MvPowerSeries.pderiv_X_of_ne (Ne.symm h), map_zero, if_neg h]
