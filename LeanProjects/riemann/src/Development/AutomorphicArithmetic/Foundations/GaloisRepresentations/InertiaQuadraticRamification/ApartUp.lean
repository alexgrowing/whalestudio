import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ThreeApartOf
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem exists_real_lift (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M]
    [Algebra K M] (x : 𝓞 (maximalRealSubfield K)) :
    ∃ y : 𝓞 (maximalRealSubfield M), algebraMap (𝓞 (maximalRealSubfield M)) (𝓞 M) y =
      algebraMap (𝓞 K) (𝓞 M) (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) x) := by
  set y₀ : 𝓞 M := algebraMap (𝓞 K) (𝓞 M) (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) x) with hy₀
  have hz : (y₀ : M) = algebraMap K M (((x : maximalRealSubfield K)) : K) := rfl
  have hmem : (y₀ : M) ∈ maximalRealSubfield M := by
    rw [hz]
    exact (mem_maximalRealSubfield_iff _).2 fun φ =>
      (mem_maximalRealSubfield_iff _).1 (x : maximalRealSubfield K).2 (φ.comp (algebraMap K M))
  have hint : IsIntegral ℤ (⟨(y₀ : M), hmem⟩ : maximalRealSubfield M) :=
    (isIntegral_algebraMap_iff (B := M) (algebraMap (maximalRealSubfield M) M).injective).1
      (RingOfIntegers.isIntegral_coe y₀)
  exact ⟨⟨⟨(y₀ : M), hmem⟩, hint⟩, RingOfIntegers.ext rfl⟩

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.apartUp :
    ApartUp := by
  intro K M _ _ _ _ _ _ _
  refine ⟨fun w₁ w₂ hap h => hap ?_, fun v => ?_⟩
  · apply HeightOneSpectrum.ext
    apply Ideal.ext
    intro x
    obtain ⟨y, hy⟩ := exists_real_lift K M x
    have h' : y ∈ (w₁.under (𝓞 (maximalRealSubfield M))).asIdeal ↔
        y ∈ (w₂.under (𝓞 (maximalRealSubfield M))).asIdeal := by rw [h]
    simp only [HeightOneSpectrum.under_asIdeal, Ideal.mem_comap, hy] at h' ⊢
    exact h'
  · have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 M)) := FaithfulSMul.algebraMap_injective _ _
    have hker : RingHom.ker (algebraMap (𝓞 K) (𝓞 M)) ≤ v.asIdeal := by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]
      exact bot_le
    haveI := v.isMaximal
    obtain ⟨Q, hQ, hQm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 M) v.asIdeal hker
    have hne : Q ≠ ⊥ := by
      rintro rfl
      apply v.ne_bot
      rw [← hQm, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 hinj]
    refine ⟨⟨Q, hQ.isPrime, hne⟩, ?_⟩
    apply HeightOneSpectrum.ext
    rw [HeightOneSpectrum.under_asIdeal]
    exact hQm
