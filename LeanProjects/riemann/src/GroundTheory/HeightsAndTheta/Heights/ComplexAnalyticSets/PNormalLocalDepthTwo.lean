import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalLocalDepthTwo
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing RingTheory.Sequence

theorem NormalLocalDepthTwo.mem_span_of_maximalIdeal_mul_le {B : Type*} [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [IsDomain B] [IsIntegrallyClosed B] (hm : ¬ (maximalIdeal B).IsPrincipal)
    {x y : B} (hx : x ≠ 0) (hy : ∀ a ∈ maximalIdeal B, ∃ b, a * y = x * b) : ∃ c, y = x * c := by
  let K := FractionRing B
  by_cases h : ∀ a ∈ maximalIdeal B, ∀ b, a * y = x * b → b ∈ maximalIdeal B
  ·
    set u : K := algebraMap B K y / algebraMap B K x with hu
    have hxK : algebraMap B K x ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective B K)).mpr hx
    let N : Submodule B K := Submodule.map (Algebra.linearMap B K) (maximalIdeal B)
    have hmbot : maximalIdeal B ≠ ⊥ := fun h0 => hm (h0 ▸ ⟨⟨0, by simp⟩⟩)
    have hN : N ≠ ⊥ := by
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmbot
      intro hN0
      have : algebraMap B K a ∈ N := Submodule.mem_map_of_mem ha
      rw [hN0, Submodule.mem_bot] at this
      exact ha0 ((map_eq_zero_iff _ (IsFractionRing.injective B K)).mp this)
    have hNfg : N.FG := (IsNoetherian.noetherian (maximalIdeal B)).map _
    have hstab : ∀ n ∈ N, u • n ∈ N := by
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨b, hb⟩ := hy a ha
      refine ⟨b, h a ha b hb, ?_⟩
      change algebraMap B K b = u * algebraMap B K a
      rw [hu, div_mul_eq_mul_div, eq_div_iff hxK, ← map_mul, ← map_mul]
      congr 1
      linear_combination -hb
    obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp
      (isIntegral_of_smul_mem_submodule N hN hNfg u hstab)
    refine ⟨c, IsFractionRing.injective B K ?_⟩
    rw [map_mul, hc, hu]
    exact (mul_div_cancel₀ _ hxK).symm
  ·
    push Not at h
    obtain ⟨a, ha, b, hab, hb⟩ := h
    have hbu : IsUnit b := by
      by_contra hb'
      exact hb ((mem_maximalIdeal b).mpr hb')
    by_cases hy0 : y = 0
    · exact ⟨0, by simp [hy0]⟩
    exfalso
    apply hm
    refine ⟨⟨a, le_antisymm ?_ ?_⟩⟩
    · intro a' ha'
      obtain ⟨b', hb'⟩ := hy a' ha'
      have hab' : a' * b = a * b' := mul_right_cancel₀ hy0 (by linear_combination b * hb' - b' * hab)
      refine Submodule.mem_span_singleton.mpr ⟨b' * ↑hbu.unit⁻¹, ?_⟩
      rw [smul_eq_mul, show b' * ↑hbu.unit⁻¹ * a = (a * b') * ↑hbu.unit⁻¹ by ring, ← hab', mul_assoc,
        hbu.mul_val_inv, mul_one]
    · rw [Ideal.submodule_span_eq, Ideal.span_le, Set.singleton_subset_iff]
      exact ha

theorem NormalLocalDepthTwo.proof : NormalLocalDepthTwo.Statement := by
  intro B _ _ _ _ _
  by_cases hfield : IsField B
  · refine ⟨[], by simp, IsWeaklyRegular.nil B B, ?_⟩
    rw [ringKrullDim_eq_zero_of_isField hfield]
    simp
  have hmbot : maximalIdeal B ≠ ⊥ := isField_iff_maximalIdeal_eq.not.mp hfield
  obtain ⟨x, hxm, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmbot
  have hxreg : IsSMulRegular B x := fun a b h => mul_left_cancel₀ hx0 h
  by_cases hp : (maximalIdeal B).IsPrincipal
  ·
    have : IsDiscreteValuationRing B := ((IsDiscreteValuationRing.TFAE B hfield).out 4 0).mp hp
    refine ⟨[x], by simpa using hxm,
      (isWeaklyRegular_cons_iff _ _ _).mpr ⟨hxreg, IsWeaklyRegular.nil _ _⟩, ?_⟩
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one]
    simp

  have hreg : ∃ y ∈ maximalIdeal B, IsSMulRegular (QuotSMulTop x B) y := by
    by_contra hcon
    push Not at hcon
    have hsub : ((maximalIdeal B : Ideal B) : Set B) ⊆
        ⋃ p ∈ associatedPrimes B (QuotSMulTop x B), (p : Set B) := by
      rw [biUnion_associatedPrimes_eq_zero_divisors]
      intro y hy
      have h1 := hcon y hy
      rw [isSMulRegular_iff_right_eq_zero_of_smul] at h1
      push Not at h1
      obtain ⟨z, hz, hz0⟩ := h1
      exact ⟨z, hz0, hz⟩
    have hmem := (Ideal.subset_iUnion_iff_mem_of_isMaximal_of_finite
      (associatedPrimes.finite B (QuotSMulTop x B)) ⊥ ⊥
      (fun I hI _ _ => IsAssociatedPrime.isPrime hI) bot_ne_top bot_ne_top).mp hsub
    obtain ⟨-, z, hz⟩ := isAssociatedPrime_iff.mp hmem
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hyx : ∀ a ∈ maximalIdeal B, ∃ b, a * y = x * b := by
      intro a ha
      rw [hz, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at ha
      obtain ⟨b, -, hb⟩ := ha
      exact ⟨b, by simpa [smul_eq_mul] using hb.symm⟩
    obtain ⟨c, hc⟩ := NormalLocalDepthTwo.mem_span_of_maximalIdeal_mul_le hp hx0 hyx
    have h1 : (1 : B) ∈ maximalIdeal B := by
      rw [hz, Submodule.mem_colon_singleton, one_smul, Submodule.mem_bot,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨c, trivial, by rw [hc, smul_eq_mul]⟩
    exact (maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  obtain ⟨y, hym, hy⟩ := hreg
  refine ⟨[x, y], ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption
  · exact (isWeaklyRegular_cons_iff _ _ _).mpr
      ⟨hxreg, (isWeaklyRegular_cons_iff _ _ _).mpr ⟨hy, IsWeaklyRegular.nil _ _⟩⟩
  · exact (min_le_left _ _).trans (by simp)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
