import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrInt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpa

open scoped TensorProduct Matrix Pointwise
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.PeriodicPositiveIntegral

theorem integral_ne_zero_of_cocompact {G : Type} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] (Γ : AddSubgroup G) [Countable Γ] {K : Set G}
    (hK : IsCompact K) (hKc : ∀ x : G, ∃ γ ∈ Γ, γ + x ∈ K)
    (I : G → ℂ) (hI : Continuous I) (hper : ∀ γ ∈ Γ, ∀ u, I (γ + u) = I u)
    (hnn : ∀ u, 0 ≤ (I u).re) (h0 : 0 < (I 0).re) (ν : Measure G) [ν.IsAddHaarMeasure] (𝓕 : Set G)
    (h𝓕 : IsAddFundamentalDomain Γ 𝓕 ν) (hfin : ν 𝓕 < ⊤) : ∫ u in 𝓕, I u ∂ν ≠ 0 := by
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hI.continuousOn
  have hint : Integrable I (ν.restrict 𝓕) := by
    refine Integrable.of_bound hI.aestronglyMeasurable C (Filter.Eventually.of_forall fun w => ?_)
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← hper γ hγ w]
    exact hC _ h
  have hcre : Continuous fun u => (I u).re := Complex.continuous_re.comp hI
  have hO : IsOpen (Function.support fun u => (I u).re) := hcre.isOpen_support
  have hpos : ν (Function.support fun u => (I u).re) ≠ 0 := hO.measure_ne_zero ν ⟨0, h0.ne'⟩
  intro hz
  have hre : ∫ u in 𝓕, (I u).re ∂ν = 0 := by
    have := integral_re (𝕜 := ℂ) hint
    rw [hz] at this
    simpa using this
  have hlt : 0 < ∫ u in 𝓕, (I u).re ∂ν := by
    rw [integral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall hnn) hint.re,
      Measure.restrict_apply hO.measurableSet, pos_iff_ne_zero]
    intro hm
    refine hpos (h𝓕.measure_zero_of_invariant _ (fun g => ?_) hm)
    ext u
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    show (I (((-g : Γ) : G) + u)).re ≠ 0 ↔ (I u).re ≠ 0
    rw [hper _ (-g).2]
  exact hlt.ne' hre

theorem integral_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ)
    (I : WOF F E nS nT → ℂ), Continuous I → (∀ γ ∈ ratLF F E nS nT, ∀ u, I (γ + u) = I u) →
    (∀ u, 0 ≤ (I u).re) → 0 < (I 0).re →
    ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν → ∫ u in 𝓕, I u ∂ν ≠ 0 := by
  intro F E _ _ _ _ _ nS nT I hI hper hnn h0 ν 𝓕 hν h𝓕
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  exact integral_ne_zero_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc I hI hper hnn h0 ν 𝓕 h𝓕
    (GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc ν h𝓕)

end GlobalTheory.PeriodicPositiveIntegral
