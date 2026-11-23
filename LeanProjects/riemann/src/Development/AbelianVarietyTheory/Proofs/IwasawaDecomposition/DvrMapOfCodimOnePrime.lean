import Mathlib
open IsLocalRing

namespace GlobalTheory

theorem trait_unramified_of_prime_below : ∀ {A R W : Type} [CommRing A] [CommRing R] [IsDomain R] [CommRing W] [IsDomain W] [IsLocalRing W] (φ : A →+* R) (Q : Ideal R) [Q.IsPrime], IsDiscreteValuationRing (Localization.AtPrime Q) → (Q.comap φ).map ((algebraMap R (Localization.AtPrime Q)).comp φ) = maximalIdeal (Localization.AtPrime Q) → ∀ (ϖ : W), Irreducible ϖ → maximalIdeal W = Ideal.span {ϖ} → ∀ g : R →+* W, (∀ r, r ∉ Q → IsUnit (g r)) → (∃ π ∈ Q, Associated (g π) ϖ) → (Q.comap φ).map (g.comp φ) = maximalIdeal W ∧ (maximalIdeal W).comap g = Q := by
  intro A R W _ _ _ _ _ _ φ Q _ hV hQ ϖ hϖ hW g hg hπ
  haveI := hV
  obtain ⟨π, hπQ, hπϖ⟩ := hπ
  have hunit : ∀ y : Q.primeCompl, IsUnit (g y) := fun y => hg y y.2
  obtain ⟨G, hGdef⟩ : ∃ G : Localization.AtPrime Q →+* W, G = IsLocalization.lift (M := Q.primeCompl) hunit := ⟨_, rfl⟩
  have hG : ∀ r, G (algebraMap R _ r) = g r := fun r => by rw [hGdef]; exact IsLocalization.lift_eq hunit r
  have hGc : G.comp (algebraMap R (Localization.AtPrime Q)) = g := by rw [hGdef]; exact IsLocalization.lift_comp hunit
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime Q)
  have hmax : maximalIdeal (Localization.AtPrime Q) = Ideal.span {t} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht
  have hϖu : ¬ IsUnit ϖ := hϖ.not_isUnit
  have hπ0 : algebraMap R (Localization.AtPrime Q) π ≠ 0 := by
    intro h0
    have : g π = 0 := by rw [← hG, h0, map_zero]
    rw [this] at hπϖ
    exact hϖ.ne_zero ((Associated.eq_zero_iff hπϖ).1 rfl)
  have hGt : ¬ IsUnit (G t) := by
    intro hu
    obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπ0 ht
    apply hϖu
    apply hπϖ.isUnit
    rw [← hG, hn, map_mul, map_pow]
    exact (u.isUnit.map G).mul (hu.pow n)
  have hmapV : (maximalIdeal (Localization.AtPrime Q)).map G = maximalIdeal W := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [hmax, Ideal.mem_span_singleton] at hx
      obtain ⟨y, rfl⟩ := hx
      rw [Ideal.mem_comap, map_mul, mem_maximalIdeal, mem_nonunits_iff]
      exact fun h => hGt (isUnit_of_mul_isUnit_left h)
    · rw [hW, Ideal.span_le, Set.singleton_subset_iff]
      obtain ⟨v, hv⟩ := hπϖ
      rw [← hv, ← hG]
      apply Ideal.mul_mem_right
      apply Ideal.mem_map_of_mem
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q π).2 hπQ
  refine ⟨?_, ?_⟩
  · rw [← hmapV, ← hQ, Ideal.map_map, ← RingHom.comp_assoc, hGc]
  · have hcm : (maximalIdeal W).comap G = maximalIdeal (Localization.AtPrime Q) := by
      symm
      apply (maximalIdeal.isMaximal _).eq_of_le
      · exact Ideal.comap_ne_top G (maximalIdeal.isMaximal W).ne_top
      · rw [← Ideal.map_le_iff_le_comap, hmapV]
    rw [← hGc, ← Ideal.comap_comap, hcm]
    exact Localization.AtPrime.comap_maximalIdeal (I := Q)

end GlobalTheory
