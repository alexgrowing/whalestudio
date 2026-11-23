import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameRankLeAndExistsRationalSwap
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittFrame_rank_le_and_exists_rational_swap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → 2 * (r + 1) ≤ n ∧ ∃ w ∈ ratPts σ J, (matHom _ σ J w).1 * adMat F Y = adMat F X ∧ (matHom _ σ J w).1 * adMat F X = adMat F Y := by
  first | exact @GlobalTheory.ResidueEisenstein.Swap.two_mul_le_and_exists_ratPts_swap | exact GlobalTheory.ResidueEisenstein.Swap.two_mul_le_and_exists_ratPts_swap | (intros; apply GlobalTheory.ResidueEisenstein.Swap.two_mul_le_and_exists_ratPts_swap <;> assumption)
