import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusKernelQuotientLePowCotangent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_frobeniusKernelQuotient_le_pow_cotangent : ∀ (q : ℕ) (K H : Type) [Field K] [CommRing H] [Bialgebra K H] [Module.Finite K H], 0 < q → Module.finrank K (H ⧸ frobKerIdeal q K H) ≤ q ^ Module.finrank K (Cot K H) := by
  first | exact @GlobalTheory.FrobKerDim.finrank_quot_frobKerIdeal_le | exact GlobalTheory.FrobKerDim.finrank_quot_frobKerIdeal_le | (intros; apply GlobalTheory.FrobKerDim.finrank_quot_frobKerIdeal_le <;> assumption)
