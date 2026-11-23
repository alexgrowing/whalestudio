import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodularQuotientIntegralFormula
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unimodular_quotient_integral_formula : ∀ (G T L : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [SecondCountableTopology T] [T2Space T]
    [MeasurableSpace T] [BorelSpace T]
    [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L] [SecondCountableTopology L] [T2Space L]
    [MeasurableSpace L] [BorelSpace L]
    (φ : T × L ≃ₜ* G) (Γ : Subgroup G) (ΓT : Subgroup T) (ΓL : Subgroup L) [DiscreteTopology ΓT],
    (∀ p : T × L, φ p ∈ Γ ↔ p.1 ∈ ΓT ∧ p.2 ∈ ΓL) →
    ∀ (A : G → ℂ) (a : L → ℂ), (∀ p : T × L, A (φ p) = a p.2) →
    (∀ (μ : Measure G) (𝓕 : Set G), μ.IsHaarMeasure → IsFundamentalDomain Γ 𝓕 μ →
      IntegrableOn A 𝓕 μ ∧ ∫ m in 𝓕, A m ∂μ = 0) →
    ∀ (μ₁ : Measure L) (𝓕₁ : Set L), μ₁.IsHaarMeasure → IsFundamentalDomain ΓL 𝓕₁ μ₁ →
      IntegrableOn a 𝓕₁ μ₁ ∧ ∫ m in 𝓕₁, a m ∂μ₁ = 0 := by
  first | exact @GlobalTheory.ProdFundDom.setIntegral_eq_zero_of_prod | exact GlobalTheory.ProdFundDom.setIntegral_eq_zero_of_prod | (intros; apply GlobalTheory.ProdFundDom.setIntegral_eq_zero_of_prod <;> assumption)
