import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DTCompDT
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_antidiagonal_dT_comp_dT_eq_zero : ∀ a b c d : ℕ, c + d + 2 = a + b → ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (c + d + 1), dT a b x.1 x.2 ≫ dT x.1 x.2 c d = 0 := by
  first | (exact @GlobalTheory.EZ.TotSq.dT_sq) | (exact GlobalTheory.EZ.TotSq.dT_sq) | (intros; apply GlobalTheory.EZ.TotSq.dT_sq  <;> assumption)
