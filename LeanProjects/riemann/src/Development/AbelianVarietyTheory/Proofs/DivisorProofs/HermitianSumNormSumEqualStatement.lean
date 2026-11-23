import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSumNormSumEqual
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeZeroTorus
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes GlobalTheory.EisRestrict
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_sum_norm_sum_equal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (w : InfinitePlace F) (k k' : ℕ) (z : Fin k → w.Completion ⊗[F] E) (z' : Fin k' → w.Completion ⊗[F] E),
    ∑ i, sigR w.Completion σ (z i) * z i = ∑ i, sigR w.Completion σ (z' i) * z' i →
    ∑ i, Algebra.norm w.Completion (z i) = ∑ i, Algebra.norm w.Completion (z' i) := by
  first | exact @GlobalTheory.CMNormSum.sum_norm_eq | exact GlobalTheory.CMNormSum.sum_norm_eq | (intros; apply GlobalTheory.CMNormSum.sum_norm_eq <;> assumption)
