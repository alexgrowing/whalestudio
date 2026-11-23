import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativeAdditive
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_derivative_additive : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) (f : GAd σ J → ℂ), IsSm σ J f →
    ∀ (X X' : Matrix (Fin n) (Fin n) ℂ) (γ δ ε : ℝ → GAd σ J), IsLineOf σ J τ X γ → IsLineOf σ J τ X' δ →
      (IsLineOf σ J τ (X + X') ε → lineDer ε f = lineDer γ f + lineDer δ f) ∧
      (IsLineOf σ J τ (X * X' - X' * X) ε → lineDer ε f = lineDer γ (lineDer δ f) - lineDer δ (lineDer γ f)) := by
  first | exact @GlobalTheory.LeviHC.LineLie.lineDer_add_bracket | exact GlobalTheory.LeviHC.LineLie.lineDer_add_bracket | (intros; apply GlobalTheory.LeviHC.LineLie.lineDer_add_bracket <;> assumption)
