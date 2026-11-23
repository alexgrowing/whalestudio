import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalEnvelopingLineDerivatives
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universal_enveloping_line_derivatives : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) (D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)), IsDer σ J τ D →
    ∀ u ∈ Algebra.adjoin ℂ (Set.range D), ∃ z : List (ℝ → GAd σ J) →₀ ℂ,
      (∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ J γ) ∧ ∀ f : SmG σ J, dop z f.1 = (u f).1 := by
  first | exact @GlobalTheory.LeviHC.WordAlg.adjoin_word | exact GlobalTheory.LeviHC.WordAlg.adjoin_word | (intros; apply GlobalTheory.LeviHC.WordAlg.adjoin_word <;> assumption)
