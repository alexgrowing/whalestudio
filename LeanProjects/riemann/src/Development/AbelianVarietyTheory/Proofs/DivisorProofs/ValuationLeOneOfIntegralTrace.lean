import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlaces
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemInverseDifferentIdealPowRealIffUnramifiedCm
open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped nonZeroDivisors

namespace GlobalTheory.CodiffValPrimeW

theorem valuation_le_one_of_mem_codiff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ B.P →
    ∀ c : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * c))) → w.valuation E c ≤ 1 := by
  intro F E _ _ _ _ _ σ B hB w hw c hc

  have hF : ¬ differentIdeal ℤ (𝓞 F) ≤ (w.under (𝓞 F)).asIdeal :=
    GlobalTheory.DiffCoprimeP.not_le_differentIdeal_of_psiUnr hB.std _ (hB.psiP _ hw)

  have hu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E) := by
    haveI := hB.unram
    infer_instance
  have hE : ¬ differentIdeal ℤ (𝓞 E) ≤ w.asIdeal := by
    rw [GlobalTheory.SnMass.SkewVol.differentIdeal_eq_map_of_unramified hu]
    intro h
    exact hF (Ideal.map_le_iff_le_comap.1 h)
  obtain ⟨d, hdD, hdw⟩ := Set.not_subset.1 hE

  have hcd : c ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))]
    intro a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hc o)
    refine ⟨n, ?_⟩
    rw [hn, Algebra.traceForm_apply, mul_comm]

  have h1 : c * (d : E) ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    have hne : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
      FractionalIdeal.dual_ne_zero ℤ ℚ (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))
    have hmul := FractionalIdeal.mul_mem_mul hcd
      ((FractionalIdeal.mem_coeIdeal _).2 ⟨d, hdD, rfl⟩ :
        (d : E) ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E))
    rwa [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), mul_inv_cancel₀ hne] at hmul
  obtain ⟨x, hx⟩ := (FractionalIdeal.mem_one_iff _).1 h1
  have hvx : w.valuation E (c * (d : E)) ≤ 1 := by
    rw [← hx]
    exact w.valuation_le_one x
  have hvd : w.valuation E (d : E) = 1 :=
    le_antisymm (w.valuation_le_one d) (not_lt.1 fun h => hdw ((w.valuation_lt_one_iff_mem d).1 h))
  rw [map_mul, hvd, mul_one] at hvx
  exact hvx

end GlobalTheory.CodiffValPrimeW
