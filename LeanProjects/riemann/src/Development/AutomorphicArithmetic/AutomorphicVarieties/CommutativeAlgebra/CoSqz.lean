import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoFinite

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.co_sqz :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (M : Type) [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [Module O M] [IsScalarTower O R M] [Module.Finite R M] [Algebra O (TrivSqZeroExt R M)],
      (∀ c : O, algebraMap O (TrivSqZeroExt R M) c = TrivSqZeroExt.inl (algebraMap O R c)) → IsCO O (TrivSqZeroExt R M) := by
  intro O _ _ R _ _ _ M _ _ _ _ _ _ _ _ hO
  haveI : IsLocalRing (TrivSqZeroExt R M) :=
    IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
      simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
      exact IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst
  haveI hST := IsScalarTower.of_algebraMap_eq (R := O) (S := R) (A := TrivSqZeroExt R M) fun c => by
    rw [hO, TrivSqZeroExt.algebraMap_eq_inl]
  haveI : Module.Finite R (TrivSqZeroExt R M) := inferInstanceAs (Module.Finite R (R × M))
  refine co_finite O R (TrivSqZeroExt R M) ?_
  intro x
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x.fst
  refine ⟨a, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, hO,
    TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl]
  rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha
