import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinHeightSmulInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsEvEqProdNormZpow
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicCharacterFrequenciesAndConductorProduct
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.RegroupAbsNorm

theorem finprod_aboveF_absNorm_zpow_count : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (I : FractionalIdeal (𝓞 E)⁰ E), I ≠ 0 →
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ∏ w ∈ Formalism.L2.Host.aboveF (L := E) F v,
        (Ideal.absNorm w.asIdeal : ℝ) ^ FractionalIdeal.count E w I = (FractionalIdeal.absNorm I : ℝ) := by
  intro F E _ _ _ _ _ I hI
  classical
  set f : HeightOneSpectrum (𝓞 E) → ℝ := fun w => (Ideal.absNorm w.asIdeal : ℝ) ^ FractionalIdeal.count E w I with hf
  have hS : (Function.mulSupport f).Finite := by
    refine (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors I)).subset fun u hu h0 => hu ?_
    simp only [hf, h0, zpow_zero]
  set S := hS.toFinset
  have key := GlobalTheory.AdeleCharConductor.finprod_absNorm_zpow_count (F := E) hI
  rw [finprod_eq_prod_of_mulSupport_subset f (s := S) (by simp [S])] at key
  rw [← key]
  have hmem : ∀ v (w : HeightOneSpectrum (𝓞 E)), w ∈ Formalism.L2.Host.aboveF (L := E) F v ↔ w.under (𝓞 F) = v := by
    intro v w
    simp [Formalism.L2.Host.aboveF]
  have hinner : ∀ v, ∏ w ∈ Formalism.L2.Host.aboveF (L := E) F v, f w = ∏ w ∈ S with w.under (𝓞 F) = v, f w := by
    intro v
    symm
    refine Finset.prod_subset (fun w hw => ?_) (fun w hw hw' => ?_)
    · rw [Finset.mem_filter] at hw
      exact (hmem v w).2 hw.2
    · have : w ∉ S := fun h => hw' (Finset.mem_filter.2 ⟨h, (hmem v w).1 hw⟩)
      simpa [S] using this
  rw [finprod_eq_prod_of_mulSupport_subset (s := S.image (fun w => w.under (𝓞 F)))]
  · rw [Finset.prod_congr rfl (fun v _ => hinner v)]
    exact Finset.prod_fiberwise_of_maps_to (fun w hw => Finset.mem_image_of_mem _ hw) f
  · intro v hv
    rw [Function.mem_mulSupport, hinner v] at hv
    obtain ⟨w, hw, hw1⟩ := Finset.exists_ne_one_of_prod_ne_one hv
    rw [Finset.mem_filter] at hw
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨w, hw.1, hw.2⟩)

end GlobalTheory.RegroupAbsNorm
