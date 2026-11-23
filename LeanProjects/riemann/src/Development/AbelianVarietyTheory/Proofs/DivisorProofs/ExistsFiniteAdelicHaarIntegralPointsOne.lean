import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicVectorsBoundsPureTensorsSlices
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableEmbeddingAdelicTupleLocalComponents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductIntegralPureTensorEqProd
open scoped Matrix GlobalTheory.VacAny ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.FinAdeleHaarNorm

open scoped RestrictedProduct Topology

theorem isCompact_integral (F : Type) [Field F] [NumberField F] :
    IsCompact {b : Af F | ∀ v : HeightOneSpectrum (𝓞 F), evalV F v b ∈ v.adicCompletionIntegers F} := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

theorem isOpen_integral (F : Type) [Field F] [NumberField F] :
    IsOpen {b : Af F | ∀ v : HeightOneSpectrum (𝓞 F), evalV F v b ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)

theorem exists_addHaar_integral_eq_one : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → Af F)] [BorelSpace (κ → Af F)],
    ∃ μf : Measure (κ → Af F), μf.IsAddHaarMeasure ∧ μf {y | ∀ i (v : HeightOneSpectrum (𝓞 F)), evalV F v (y i) ∈ v.adicCompletionIntegers F} = 1 := by
  intro F _ _ κ _ _ _
  set U : Set (κ → Af F) := {y | ∀ i (v : HeightOneSpectrum (𝓞 F)), evalV F v (y i) ∈ v.adicCompletionIntegers F}
  have hU : U = Set.pi Set.univ (fun _ : κ =>
      {b : Af F | ∀ v : HeightOneSpectrum (𝓞 F), evalV F v b ∈ v.adicCompletionIntegers F}) := by
    ext y; simp [U]
  have hc : IsCompact U := hU ▸ isCompact_univ_pi (fun _ => isCompact_integral F)
  have ho : IsOpen U := hU ▸ isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_integral F)
  have h0 : (0 : κ → Af F) ∈ U := fun i v => by simp
  let K₀ : TopologicalSpace.PositiveCompacts (κ → Af F) :=
    ⟨⟨U, hc⟩, ⟨0, ho.interior_eq.symm ▸ h0⟩⟩
  exact ⟨Measure.addHaarMeasure K₀, inferInstance, Measure.addHaarMeasure_self⟩

end GlobalTheory.FinAdeleHaarNorm
