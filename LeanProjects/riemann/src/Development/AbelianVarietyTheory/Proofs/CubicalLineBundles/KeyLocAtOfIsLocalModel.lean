import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyPBId

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem mem_range_iff_valuation_le_one {R K Γ : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (hR : ∀ r : R, v (algebraMap R K r) ≤ 1) {π : K} (hπ0 : v π ≠ 0) (hπ : v π < 1) (y : K) :
    y ∈ Set.range (algebraMap R K) ↔ v y ≤ 1 := by
  refine ⟨fun ⟨r, hr⟩ => hr ▸ hR r, fun hy => ?_⟩
  have hu : ∀ u : Rˣ, v (algebraMap R K u) = 1 := fun u => by
    refine le_antisymm (hR _) ?_
    have h1 : v (algebraMap R K u) * v (algebraMap R K (u⁻¹ : Rˣ)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    calc (1 : Γ) = _ := h1.symm
      _ ≤ v (algebraMap R K u) * 1 := mul_le_mul_right (hR _) _
      _ = _ := _root_.mul_one _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hlt : v (algebraMap R K ϖ) < 1 := by
    refine lt_of_le_of_ne (hR _) fun h => ?_
    rcases ValuationRing.isInteger_or_isInteger R π with ⟨r, hr⟩ | ⟨r, hr⟩
    · have hr0 : r ≠ 0 := by
        rintro rfl
        rw [map_zero] at hr
        exact hπ0 (by rw [← hr, map_zero])
      obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hϖ
      rw [← hr, map_mul, map_mul, hu, map_pow, map_pow, h, one_pow, _root_.mul_one] at hπ
      exact lt_irrefl _ hπ
    · have := hR r
      rw [hr, map_inv₀, inv_le_one₀ (zero_lt_iff.2 hπ0)] at this
      exact absurd hπ (not_lt.2 this)
  rcases ValuationRing.isInteger_or_isInteger R y with h | ⟨r, hr⟩
  · exact h
  · by_cases hy0 : y = 0
    · exact ⟨0, by rw [hy0, map_zero]⟩
    by_cases hr' : IsUnit r
    · obtain ⟨u, rfl⟩ := hr'
      refine ⟨(u⁻¹ : Rˣ), ?_⟩
      rw [← inv_inv y, ← hr]
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
    · exfalso
      have hm : r ∈ IsLocalRing.maximalIdeal R := hr'
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
      obtain ⟨s, rfl⟩ := hm
      have h1 : v y⁻¹ < 1 := by
        rw [← hr, map_mul, map_mul]
        calc _ ≤ v (algebraMap R K ϖ) * 1 := mul_le_mul_right (hR _) _
          _ < 1 := by rwa [_root_.mul_one]
      rw [map_inv₀, inv_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff v).2 hy0))] at h1
      exact absurd hy (not_le.2 h1)

theorem keyLocAt_of_isLocalModel : ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (p : HeightOneSpectrum (𝓞 K)) (a : K) (M : Matrix (Fin x.P.g) (Fin x.P.g) K), KeyPow.IsLocalModel x p a M → IsLocGen p a T.I → IsLocGen p M.det abelian₂.I → KeyLocAt x T abelian₂ p := by
  intro K _ _ x T abelian₂ p a M hM ha hd
  obtain ⟨R, _, _, _, _, _, y, th', hth', v', hv', hR, h1, h2, h3⟩ := hM
  obtain ⟨π, hπ⟩ := p.valuation_exists_uniformizer K
  refine ⟨K, inferInstance, inferInstance, R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    RingHom.id K, x, a, M.det, a, M.det, 1, 1, GlobalTheory.keyPB_id K x, ⟨th', hth', v', hv', M, y, h1, h2, rfl, h3⟩,
    fun z => ?_, by simp, by simp, ha, hd⟩
  refine mem_range_iff_valuation_le_one (p.valuation K) hR (π := π) (hπ ▸ WithZero.exp_ne_zero) ?_ z
  rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  decide

end GlobalTheory.LamF
