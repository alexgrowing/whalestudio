import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviLinesSmoothFunctionSpan
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfIsSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineToGAdDerivative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativeAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPlaneConstantTermGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtFoldrLineDer
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC
open GlobalTheory.Orb (archMat)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_lines_smooth_function_span : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) (f : GAd σ J → ℂ), GlobalTheory.UAut.IsSm σ J f →
    ∀ (ι : Type) [Fintype ι] (Y : ι → Matrix (Fin n) (Fin n) ℂ) (δ : ι → ℝ → GAd σ J) (c : ι → ℝ) (γ : ℝ → GAd σ J),
      (∀ j, GlobalTheory.LeviHC.IsLineOf σ J τ (Y j) (δ j)) → GlobalTheory.LeviHC.IsLineOf σ J τ (∑ j, c j • Y j) γ →
      GlobalTheory.SiegelSet.lineDer γ f = ∑ j, (c j : ℂ) • GlobalTheory.SiegelSet.lineDer (δ j) f := by
  first | exact @GlobalTheory.LeviHC.LineLie.lineDer_sum_smul | exact GlobalTheory.LeviHC.LineLie.lineDer_sum_smul | (intros; apply GlobalTheory.LeviHC.LineLie.lineDer_sum_smul <;> assumption)
