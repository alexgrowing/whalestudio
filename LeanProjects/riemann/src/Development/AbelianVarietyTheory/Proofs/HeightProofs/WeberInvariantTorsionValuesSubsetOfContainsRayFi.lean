import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PrincipalRayPrimesSplitCompletelyWeberValuesStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompleteSplittingCompositumDegreeOnePrimeStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer

set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.WeberIn

theorem finite_mem {K : Type} [Field K] [NumberField K] {a : 𝓞 K} (ha : a ≠ 0) :
    {𝔭 : HeightOneSpectrum (𝓞 K) | a ∈ 𝔭.asIdeal}.Finite := by
  have h : Ideal.span {a} ≠ (0 : Ideal (𝓞 K)) := by
    simpa [Ideal.span_singleton_eq_bot] using ha
  refine (Ideal.finite_factors h).subset ?_
  intro 𝔭 h𝔭
  exact Ideal.dvd_span_singleton.2 h𝔭

theorem finite_norm_mem {K : Type} [Field K] [NumberField K] (S : Finset ℕ) :
    {𝔭 : HeightOneSpectrum (𝓞 K) | Ideal.absNorm 𝔭.asIdeal ∈ S}.Finite := by
  have h : {I : Ideal (𝓞 K) | Ideal.absNorm I ≠ 0 ∧ Ideal.absNorm I ∈ S}.Finite := by
    refine (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) (S.sup id)).subset ?_
    intro I hI
    exact Finset.le_sup (f := id) hI.2
  refine (h.preimage (f := fun 𝔭 : HeightOneSpectrum (𝓞 K) => 𝔭.asIdeal)
    (fun a _ b _ hab => HeightOneSpectrum.ext hab)).subset ?_
  intro 𝔭 h𝔭
  exact ⟨fun h0 => 𝔭.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0), h𝔭⟩

theorem numberField_adjoin (K L : IntermediateField ℚ ℂ) [NumberField L] (S : Set ℂ)
    [NumberField (IntermediateField.adjoin K S)] : NumberField (IntermediateField.adjoin L S) := by
  have h1 : FiniteDimensional ℚ ((IntermediateField.adjoin K S).restrictScalars ℚ) :=
    (inferInstance : FiniteDimensional ℚ (IntermediateField.adjoin K S))
  have hle : IntermediateField.adjoin ℚ S ≤ (IntermediateField.adjoin K S).restrictScalars ℚ :=
    IntermediateField.adjoin_le_iff.2 (IntermediateField.subset_adjoin K S)
  have h2 : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  have h3 : FiniteDimensional ℚ ((IntermediateField.adjoin L S).restrictScalars ℚ) := by
    have e := IntermediateField.restrictScalars_adjoin_eq_sup ℚ L S
    have h5 : FiniteDimensional ℚ (L ⊔ IntermediateField.adjoin ℚ S : IntermediateField ℚ ℂ) := inferInstance
    rw [← e] at h5
    exact h5
  have h4 : FiniteDimensional ℚ (IntermediateField.adjoin L S) := h3
  exact NumberField.mk

theorem weberSet_subset : ∀ (K L : IntermediateField ℚ ℂ) [NumberField K] [NumberField L] [IsTotallyComplex K] (h : K ≤ L), Module.finrank ℚ K = 2 → discr K < -4 → ∀ P : PeriodPair, (∀ z, z ∈ P.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ n : ℕ, 3 ≤ n → GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (IntermediateField.inclusion h).toRingHom n → weberSet P n ⊆ L := by
  intro K L _ _ _ h h2 hd P hP n hn hR
  obtain ⟨inst, S, hS⟩ := GlobalTheory.T.principalRayPrimes_splitCompletely_weberValues K h2 hd P hP n hn
  haveI := numberField_adjoin K L (weberSet P n)
  have hn0 : (n : 𝓞 L) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  haveI : NumberField (⊥ : IntermediateField L ℂ) := NumberField.of_module_finite L _
  have hle : IntermediateField.adjoin L (weberSet P n) ≤ ⊥ := by
    refine GlobalTheory.Bauer.le_of_finite_split_not_split L ℂ ⊥ (IntermediateField.adjoin L (weberSet P n)) ?_
    refine ((finite_mem hn0).union (finite_norm_mem S)).subset ?_
    rintro 𝔓 ⟨hp, -, hnot⟩
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hc
    obtain ⟨f, α, hN, hα, h1⟩ := hR 𝔓 hc.1
    have hf : f = 1 := by
      have hp' := hp
      rw [hN] at hp'
      exact hp'.eq_one_of_pow
    subst hf
    rw [pow_one] at hN hα
    have hne : 𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (IntermediateField.inclusion h).toRingHom) ≠ ⊥ := by
      intro h0
      rw [h0, Ideal.absNorm_bot] at hN
      exact hp.ne_zero hN
    haveI := 𝔓.isPrime
    let 𝔭 : HeightOneSpectrum (𝓞 K) :=
      ⟨𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (IntermediateField.inclusion h).toRingHom),
        Ideal.comap_isPrime _ _, hne⟩
    apply hnot
    refine GlobalTheory.T.completeSplitting_compositum_degreeOnePrime K L h (weberSet P n) 𝔭 𝔓 rfl hN ?_
    have h𝔭 : 𝔭.asIdeal = Ideal.span {α} := hα
    rw [h𝔭]
    exact hS α _ hp hc.2 (by rw [← hα, ← hN]) (Ideal.mem_span_singleton.2 h1)
  intro x hx
  have hx' := hle (IntermediateField.subset_adjoin L _ hx)
  obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.1 hx'
  exact y.2

end GlobalTheory.FieldSize.WeberIn
