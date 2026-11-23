import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactStandardParabolicUnipotentRadicalWittFrStatement
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

namespace GlobalTheory.StdPar

theorem exists_haar_fundamentalDomain_mass_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E),
      GlobalTheory.SiegelSet.IsWittFrame σ J X Y → ∀ S : Finset (Fin r),
      ∃ (μ : Measure (GlobalTheory.StdPar.unip σ J X S)) (𝓕 : Set (GlobalTheory.StdPar.unip σ J X S)), μ.IsHaarMeasure ∧
        IsFundamentalDomain ((ratPts σ J).subgroupOf (GlobalTheory.StdPar.unip σ J X S)) 𝓕 μ ∧ μ 𝓕 = 1 := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S
  haveI : LocallyCompactSpace (unip σ J X S) := (isClosed_unip S h hJ hW).locallyCompactSpace
  have hc := GlobalTheory.T.cocompact_standardParabolicUnipotentRadical_wittFrame F E σ h n J hJ r X Y hW S
  have hd := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom ((ratPts σ J).subgroupOf (unip σ J X S))
    (Measure.haar : Measure (unip σ J X S))
  have h0 : (Measure.haar : Measure (unip σ J X S)) (GlobalTheory.AutomorphicL2Unitary.stdDom _) ≠ 0 := hd.measure_ne_zero (NeZero.ne _)
  have ht : (Measure.haar : Measure (unip σ J X S)) (GlobalTheory.AutomorphicL2Unitary.stdDom _) ≠ ⊤ := hc.measure_ne_top hd
  refine ⟨((Measure.haar : Measure (unip σ J X S)) (GlobalTheory.AutomorphicL2Unitary.stdDom _))⁻¹ • Measure.haar, GlobalTheory.AutomorphicL2Unitary.stdDom _,
    Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 ht) (ENNReal.inv_ne_top.2 h0),
    GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ _, ?_⟩
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 ht]

end GlobalTheory.StdPar
