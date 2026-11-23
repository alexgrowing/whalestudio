import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwOCommD
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dD_comp_awO_eq_sum_awO_comp_dT : ∀ (n a b : ℕ), a + b = n → dD (n + 1) n ≫ awO n a b = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 a b := by
  first | (exact @GlobalTheory.EZ.awO_comm_d) | (exact GlobalTheory.EZ.awO_comm_d) | (intros; apply GlobalTheory.EZ.awO_comm_d <;> assumption)
