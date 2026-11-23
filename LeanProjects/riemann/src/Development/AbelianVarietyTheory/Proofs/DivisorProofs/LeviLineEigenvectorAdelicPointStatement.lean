import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviLineEigenvectorAdelicPoint
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchUnipotentRadicalMem
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC
open GlobalTheory.Orb (archMat)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_line_eigenvector_adelic_point : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (w : InfinitePlace F) (τ : EmbOver E w)
      (Y : Matrix (Fin n) (Fin n) ℂ) (l : ℂ), Y *ᵥ (fun i => τ.1 (x i)) = l • (fun i => τ.1 (x i)) →
      ∀ β : ℝ → GAd σ J, GlobalTheory.LeviHC.IsLineOf σ J τ Y β → ∀ s, ∃ t : AF F ⊗[F] E,
        (matHom _ σ J (β s)).1 *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = t • fun i => inclR (F := F) (AF F) (x i) := by
  first | exact @GlobalTheory.TorFin.line_mulVec_eq_smul | exact GlobalTheory.TorFin.line_mulVec_eq_smul | (intros; apply GlobalTheory.TorFin.line_mulVec_eq_smul <;> assumption)
