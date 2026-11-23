import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFiniteAdelicDenominator
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.Reductions.SiegelPar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumFrameIdem
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_finite_adelic_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Set (Af F ⊗[F] E)), IsCompact L → ∃ d : ℕ, 0 < d ∧ ∀ e : E, inclR (F := F) (Af F) e ∈ L → IsIntegral ℤ ((d : E) * e) := by
  first | exact @GlobalTheory.CompanionTheory.AdeleDenom.exists_nat_mul_isIntegral_of_isCompact | exact GlobalTheory.CompanionTheory.AdeleDenom.exists_nat_mul_isIntegral_of_isCompact | (intros; apply GlobalTheory.CompanionTheory.AdeleDenom.exists_nat_mul_isIntegral_of_isCompact <;> assumption)
