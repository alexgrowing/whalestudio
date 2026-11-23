import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLineDerivativeCommutator
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_line_derivative_commutator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ γ δ : ℝ → GAd σ J, GlobalTheory.SiegelSet.IsRealLine σ J γ → GlobalTheory.SiegelSet.IsRealLine σ J δ →
      ∃ ε : ℝ → GAd σ J, GlobalTheory.SiegelSet.IsRealLine σ J ε ∧ ∀ f, GlobalTheory.UAut.IsSm σ J f →
        GlobalTheory.SiegelSet.lineDer γ (GlobalTheory.SiegelSet.lineDer δ f) =
          GlobalTheory.SiegelSet.lineDer δ (GlobalTheory.SiegelSet.lineDer γ f) + GlobalTheory.SiegelSet.lineDer ε f := by
  first | exact @GlobalTheory.LeviHC.LineBracket.exists_line_bracket | exact GlobalTheory.LeviHC.LineBracket.exists_line_bracket | (intros; apply GlobalTheory.LeviHC.LineBracket.exists_line_bracket <;> assumption)
