import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.spRoots :
    ∀ (R : Type) [CommRing R] (q n : ℕ) (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R) (j : Fin q), (∏ i, (Polynomial.X - Polynomial.C (Sp.u P ut j i))) = (P j).map (algebraMap R (Sp P ut)) ∧ ∀ i, Sp.u P ut j i - algebraMap R (Sp P ut) (ut j i) = Sp.mk P ut (MvPowerSeries.X (j, i)) := by
  intro R _ q n P ut j
  have hC : ∀ a : R, Sp.mk P ut (MvPowerSeries.C a) = algebraMap R (Sp P ut) a := fun a =>
    (Sp.mk P ut).commutes a
  refine ⟨?_, fun i => ?_⟩
  · have h1 : (∏ i, (Polynomial.X - Polynomial.C (Sp.u P ut j i))) =
        (∏ i, (Polynomial.X - Polynomial.C (MvPowerSeries.C (ut j i) + MvPowerSeries.X (j, i) : MvPowerSeries (Fin q × Fin n) R))).map (Sp.mk P ut).toRingHom := by
      rw [Polynomial.map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      rfl
    rw [h1]
    ext k
    rw [Polynomial.coeff_map, Polynomial.coeff_map, ← hC]
    refine (Ideal.Quotient.eq (I := spIdeal P ut)).2 ?_
    exact Ideal.subset_span ⟨j, k, by rw [Polynomial.coeff_sub, Polynomial.coeff_map]⟩
  · rw [Sp.u, map_add, hC, add_sub_cancel_left]
