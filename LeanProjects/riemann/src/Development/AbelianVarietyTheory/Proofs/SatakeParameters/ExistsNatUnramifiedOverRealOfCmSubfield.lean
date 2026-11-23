import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSqrtTotallyNegative
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraMapMemMaximalRealSubfieldIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnramifiedAdjoinSqrtOfNotMem
open NumberField IsDedekindDomain

theorem GlobalTheory.exists_nat_unramified_over_real_of_cm_subfield :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ N : ℕ, N ≠ 0 ∧ ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra E K] (w : HeightOneSpectrum (𝓞 K)), (N : 𝓞 K) ∉ w.asIdeal → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield K)) w.asIdeal := by
  intro E _ _ _
  obtain ⟨d, s, hs, hsn, -⟩ := GlobalTheory.CMGen.exists_sqrt_totallyNegative E
  have hd0 : d ≠ 0 := by
    rintro rfl
    apply hsn
    have : s = 0 := by simpa using hs
    rw [this]
    exact zero_mem _
  have h2d : (2 * d : 𝓞 (maximalRealSubfield E)) ≠ 0 := mul_ne_zero two_ne_zero hd0
  refine ⟨Ideal.absNorm (Ideal.span {2 * d}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact h2d
  intro K _ _ _ _ w hw
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {2 * d}))
  haveI : Algebra.IsAlgebraic E K := Algebra.IsAlgebraic.tower_top (K := ℚ) E
  have hint : ∀ x : 𝓞 (maximalRealSubfield E),
      IsIntegral ℤ (algebraMap E K ((x : maximalRealSubfield E) : E)) := fun x =>
    (RingOfIntegers.isIntegral_coe x).map
      ((algebraMap E K).comp (maximalRealSubfield E).subtype).toIntAlgHom
  have hmem : algebraMap E K ((d : maximalRealSubfield E) : E) ∈ maximalRealSubfield K :=
    (GlobalTheory.algebraMap_mem_maximalRealSubfield_iff _).2 (d : maximalRealSubfield E).2
  have hai : IsIntegral ℤ (⟨_, hmem⟩ : maximalRealSubfield K) :=
    (isIntegral_algHom_iff (maximalRealSubfield K).subtype.toIntAlgHom Subtype.val_injective).1 (hint d)
  let a : 𝓞 (maximalRealSubfield K) := ⟨_, hai⟩
  refine GlobalTheory.unramified_adjoin_sqrt_of_not_mem K a (algebraMap E K s) ?_ ?_ w ?_
  · rw [← map_pow, hs]; rfl
  · exact fun h => hsn ((GlobalTheory.algebraMap_mem_maximalRealSubfield_iff _).1 h)
  · intro h
    apply hw
    have h1 : algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) (2 * a) ∈ w.asIdeal := h
    let c' : 𝓞 K := ⟨_, hint c⟩
    have h2 : ((Ideal.absNorm (Ideal.span {2 * d}) : ℕ) : 𝓞 K)
        = c' * algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) (2 * a) := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      let f : 𝓞 (maximalRealSubfield E) →+* K :=
        ((algebraMap E K).comp (maximalRealSubfield E).subtype).comp (algebraMap _ _)
      have h3 := congrArg f hc
      rw [map_natCast, map_mul, map_mul, map_ofNat] at h3
      rw [map_natCast, ← h3, map_mul, map_mul, map_mul, map_ofNat, map_ofNat]
      rfl
    rw [h2]
    exact Ideal.mul_mem_left _ _ h1
