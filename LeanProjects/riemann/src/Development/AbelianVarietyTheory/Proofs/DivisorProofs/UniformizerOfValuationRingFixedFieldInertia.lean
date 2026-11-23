import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixedFieldMaximalIdealDvdUniformizer
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.InertiaFixedUniformizer

theorem valuation_uniformizer_lt_one {R K Ω : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω) (hV : IsAbove R K V.toSubring)
    {π : R} (hπ : Irreducible π) : V.valuation (algebraMap K Ω (algebraMap R K π)) < 1 := by
  have hπ0 : algebraMap R K π ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective R K)]
    exact hπ.ne_zero
  have hle : V.valuation (algebraMap K Ω (algebraMap R K π)) ≤ 1 := by
    rw [V.valuation_le_one_iff]
    have : algebraMap R K π ∈ (V.toSubring).comap (algebraMap K Ω) := by
      rw [hV]; exact ⟨π, rfl⟩
    exact this
  refine lt_of_le_of_ne hle fun h1 => hπ.not_isUnit ?_
  have hinv : (algebraMap R K π)⁻¹ ∈ (V.toSubring).comap (algebraMap K Ω) := by
    change algebraMap K Ω (algebraMap R K π)⁻¹ ∈ V
    rw [← V.valuation_le_one_iff, map_inv₀, map_inv₀, h1, inv_one]
  rw [hV] at hinv
  obtain ⟨u, hu⟩ := hinv
  refine IsUnit.of_mul_eq_one u (IsFractionRing.injective R K ?_)
  rw [map_mul, hu, mul_inv_cancel₀ hπ0, map_one]

theorem uniformizer_fixedField_inertia : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ π : R, Irreducible π →
    V.valuation (algebraMap K Ω (algebraMap R K π)) < 1 ∧
      ∀ y : IntermediateField.fixedField (inertia K V), V.valuation (y : Ω) < 1 →
        ∃ z : IntermediateField.fixedField (inertia K V), (z : Ω) ∈ V ∧
          y = algebraMap K _ (algebraMap R K π) * z := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV π hπ
  refine ⟨valuation_uniformizer_lt_one V hV hπ, fun y hy => ?_⟩
  have hπ0 : algebraMap R K π ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective R K)]
    exact hπ.ne_zero
  have hmem := GlobalTheory.FixInertUnram.div_uniformizer_mem R K Ω V hV π hπ (y : Ω) y.2
    ((ValuationSubring.mem_nonunits_iff _).2 hy)
  refine ⟨y / algebraMap K _ (algebraMap R K π), ?_, ?_⟩
  · simpa using hmem
  · rw [mul_div_cancel₀]
    exact (map_ne_zero _).2 hπ0

end GlobalTheory.InertiaFixedUniformizer
