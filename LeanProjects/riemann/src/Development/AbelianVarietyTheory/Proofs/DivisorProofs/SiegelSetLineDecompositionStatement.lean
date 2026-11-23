import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetLineDecomposition
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
theorem _root_.GlobalTheory.T.siegel_set_line_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ x : Fin n → E, hE σ J x x = 0 → ∀ K : Subgroup (GAd σ J), GlobalTheory.UAut.IsMaxCpt σ J K → ∀ S : Set (GAd σ J), IsCompact S →
    ∀ γ : ℝ → GAd σ J, GlobalTheory.SiegelSet.IsRealLine σ J γ →
      ∃ (e e' : ℕ) (β : Fin e → ℝ → GAd σ J) (ζ : Fin e' → ℝ → GAd σ J) (C : ℝ),
        (∀ j, GlobalTheory.SiegelSet.IsRealLine σ J (β j) ∧ ∀ s, ∃ t : AF F ⊗[F] E,
          (matHom _ σ J (β j s)).1 *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = t • fun i => inclR (F := F) (AF F) (x i)) ∧
        (∀ j, GlobalTheory.SiegelSet.IsRealLine σ J (ζ j) ∧ ∀ s, ζ j s ∈ K) ∧
        ∀ k ∈ S, ∃ (c : Fin e → ℂ) (c' : Fin e' → ℂ), (∀ j, ‖c j‖ ≤ C) ∧ (∀ j, ‖c' j‖ ≤ C) ∧
          ∀ f, GlobalTheory.UAut.IsSm σ J f → GlobalTheory.SiegelSet.lineDer γ f =
            ∑ j, c j • GlobalTheory.SiegelSet.lineDer (fun s => k⁻¹ * β j s * k) f + ∑ j, c' j • GlobalTheory.SiegelSet.lineDer (ζ j) f := by
  first | exact @GlobalTheory.GrowthDec.dec | exact GlobalTheory.GrowthDec.dec | (intros; apply GlobalTheory.GrowthDec.dec <;> assumption)
