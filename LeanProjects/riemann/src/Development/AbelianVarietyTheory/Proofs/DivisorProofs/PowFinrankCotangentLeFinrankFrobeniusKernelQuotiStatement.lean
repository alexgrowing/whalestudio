import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_finrank_cotangent_le_finrank_frobeniusKernelQuotient : ∀ (p : ℕ) [Fact p.Prime] (k H : Type) [Field k] [CharP k p] [CommRing H] [HopfAlgebra k H] [Module.Finite k H], p ^ Module.finrank k (Cot k H) ≤ Module.finrank k (H ⧸ frobKerIdeal p k H) := by
  first | exact @GlobalTheory.PDiv.FrobKerOrder.pow_finrank_cot_le | exact GlobalTheory.PDiv.FrobKerOrder.pow_finrank_cot_le | (intros; apply GlobalTheory.PDiv.FrobKerOrder.pow_finrank_cot_le <;> assumption)
