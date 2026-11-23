import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicVectorsBoundsPureTensorsSlices
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableEmbeddingAdelicTupleLocalComponents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductIntegralPureTensorEqProd
open scoped Matrix GlobalTheory.VacAny ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

namespace GlobalTheory.WeilAdm.HaarSplit

theorem lintegral_split_mul : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)]
    [MeasurableSpace (κ → mixedEmbedding.mixedSpace F)] [BorelSpace (κ → mixedEmbedding.mixedSpace F)]
    [MeasurableSpace (κ → Af F)] [BorelSpace (κ → Af F)]
    (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure] (μi : Measure (κ → mixedEmbedding.mixedSpace F)) [μi.IsAddHaarMeasure]
    (μf : Measure (κ → Af F)) [μf.IsAddHaarMeasure],
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ (fi : (κ → mixedEmbedding.mixedSpace F) → ℝ≥0∞) (g : (κ → Af F) → ℝ≥0∞),
      Measurable fi → Measurable g →
        ∫⁻ x, fi (fun i => evI F (x i)) * g (fun i => sndA F (x i)) ∂μ = c * ((∫⁻ z, fi z ∂μi) * ∫⁻ y, g y ∂μf) := by
  intro F _ _ κ _ mA _ mI _ mf _ μ _ μi _ μf _
  haveI : LocallyCompactSpace (Af F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (Af F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  haveI : BorelSpace ((κ → mixedEmbedding.mixedSpace F) × (κ → Af F)) := Prod.borelSpace
  haveI : (μi.prod μf).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure μi μf
  have hH : ((μ.map (splitE F κ).symm)).IsAddHaarMeasure :=
    (splitE F κ).symm.isAddHaarMeasure_map μ (continuous_splitE_symm F κ) (continuous_splitE F κ)
  let em : (κ → AF F) ≃ᵐ ((κ → mixedEmbedding.mixedSpace F) × (κ → Af F)) :=
    (Homeomorph.mk (splitE F κ).symm.toEquiv (continuous_splitE_symm F κ) (continuous_splitE F κ)).toMeasurableEquiv
  set c : NNReal := Measure.addHaarScalarFactor (μ.map (splitE F κ).symm) (μi.prod μf) with hc
  have heq : μ.map (splitE F κ).symm = c • (μi.prod μf) :=
    Measure.isAddLeftInvariant_eq_smul _ _
  refine ⟨(c : ℝ≥0∞), ?_, ENNReal.coe_ne_top, ?_⟩
  · exact ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  intro fi g hfi hg
  have h1 : ∫⁻ x, fi (fun i => evI F (x i)) * g (fun i => sndA F (x i)) ∂μ
      = ∫⁻ p, fi p.1 * g p.2 ∂(μ.map (splitE F κ).symm) := by
    rw [show μ.map (splitE F κ).symm = μ.map em from rfl, lintegral_map_equiv]
    rfl
  rw [h1, heq, lintegral_smul_measure, lintegral_prod_mul hfi.aemeasurable hg.aemeasurable]
  rfl

end GlobalTheory.WeilAdm.HaarSplit
