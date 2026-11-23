import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem spec_fraction_field_isPullback_of_unramified : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → IsPullback (spMap (algebraMap W K')) (spMap (algebraMap K K')) (spMap (algebraMap R W)) (spMap (algebraMap R K)) := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmax

  have hRK' : Function.Injective (algebraMap R K') := by
    rw [IsScalarTower.algebraMap_eq R K K']
    exact (algebraMap K K').injective.comp (IsFractionRing.injective R K)
  have hRW : Function.Injective (algebraMap R W) := by
    rw [IsScalarTower.algebraMap_eq R W K'] at hRK'
    exact Function.Injective.of_comp hRK'

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖW : Irreducible (algebraMap R W ϖ) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hmax,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid W (nonZeroDivisors R)) K' := by
    rw [IsLocalization.iff_of_le_of_exists_dvd (M := Algebra.algebraMapSubmonoid W (nonZeroDivisors R))
      (S := K') (nonZeroDivisors W)]
    · infer_instance
    · rintro _ ⟨r, hr, rfl⟩
      refine mem_nonZeroDivisors_of_ne_zero ?_
      intro h0
      exact nonZeroDivisors.ne_zero hr (hRW (by rw [h0, map_zero]))
    · intro w hw
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (nonZeroDivisors.ne_zero hw) hϖW
      refine ⟨algebraMap R W (ϖ ^ n), ⟨ϖ ^ n, mem_nonZeroDivisors_of_ne_zero
        (pow_ne_zero _ hϖ.ne_zero), rfl⟩, ?_⟩
      refine ⟨(↑u⁻¹ : W), ?_⟩
      rw [hu, map_pow, _root_.mul_comm (u : W), _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
  have hpo : Algebra.IsPushout R W K K' :=
    (Algebra.isLocalization_iff_isPushout (nonZeroDivisors R) K).mp hloc
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_iff_isPushout.mpr hpo)

end GlobalTheory
