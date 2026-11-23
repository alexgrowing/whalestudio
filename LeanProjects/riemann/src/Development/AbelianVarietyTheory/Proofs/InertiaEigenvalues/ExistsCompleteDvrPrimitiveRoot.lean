import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing

namespace GlobalTheory.CyclotomicCompletion

theorem exists_place_above (K : Type) [Field K] [NumberField K] {l : ℕ} (hl : l.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 K), (l : 𝓞 K) ∈ v.asIdeal := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl
  have : (Ideal.span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  obtain ⟨Q, hQ, hQ'⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
    (S := 𝓞 K) (Ideal.span {(l : ℤ)}) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int (algebraMap ℤ (𝓞 K)))]; exact bot_le)
  have hmem : (l : 𝓞 K) ∈ Q := by
    have : (l : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      rw [hQ']; exact Ideal.mem_span_singleton_self _
    simpa [Ideal.mem_comap] using this
  refine ⟨⟨Q, hQ, ?_⟩, hmem⟩
  rintro rfl
  exact hl.ne_zero (by simpa using hmem)

theorem exists_complete_dvr_primitiveRoot : ∀ l : ℕ, l.Prime → ∃ (O : Type) (_ : CommRing O)
    (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
    (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (_ : CharZero O),
    ¬ IsUnit (l : O) ∧ ∃ ζ : O, IsPrimitiveRoot ζ l := by
  intro l hl
  have : NeZero l := ⟨hl.ne_zero⟩
  let K : Type := CyclotomicField l ℚ
  obtain ⟨v, hv⟩ := exists_place_above K hl
  have hinj : Function.Injective (algebraMap (𝓞 K) (v.adicCompletionIntegers K)) :=
    FaithfulSMul.algebraMap_injective _ _
  have hc : IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K))
      (v.adicCompletionIntegers K) := by
    refine NormIntegers.isAdicComplete_of_fg (C := v.adicCompletion K) ⟨?_, ?_, ?_⟩
      (IsNoetherian.noetherian _) (maximalIdeal.isMaximal _).ne_top
    · exact FaithfulSMul.algebraMap_injective _ _
    · intro x
      have : ‖(x : v.adicCompletion K)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 x.2
      exact_mod_cast this
    · intro x hx
      have : ‖x‖ ≤ 1 := by exact_mod_cast hx
      exact ⟨⟨x, Valued.toNormedField.norm_le_one_iff.1 this⟩, rfl⟩
  refine ⟨v.adicCompletionIntegers K, inferInstance, inferInstance, inferInstance, hc,
    charZero_of_injective_algebraMap hinj, ?_, ?_⟩
  · rw [← map_natCast (algebraMap (𝓞 K) (v.adicCompletionIntegers K)),
      adicCompletionIntegers.isUnit_iff_valued_eq_one, algebraMap_adicCompletionIntegers_apply,
      valuedAdicCompletion_eq_valuation', valuation_eq_one_iff_notMem]
    exact fun h => h hv
  · have : IsCyclotomicExtension {l} ℚ K := CyclotomicField.isCyclotomicExtension l ℚ
    have hζ := IsCyclotomicExtension.zeta_spec l ℚ K
    exact ⟨_, hζ.toInteger_isPrimitiveRoot.map_of_injective hinj⟩

end GlobalTheory.CyclotomicCompletion
