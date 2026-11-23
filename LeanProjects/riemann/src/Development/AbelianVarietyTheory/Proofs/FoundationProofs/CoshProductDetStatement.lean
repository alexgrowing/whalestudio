import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoshProductDet
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SingularValueFrame
open scoped Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosh_product_det : ∀ (n : ℕ) (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ), IsInP ε X → ((2 : ℂ)⁻¹ • (1 + NormedSpace.exp X * NormedSpace.exp X)).det = ((coshProd ε X ^ 2 : ℝ) : ℂ) := by
  first | exact @GlobalTheory.DetExpP.det_half_one_add_exp_mul_exp | exact GlobalTheory.DetExpP.det_half_one_add_exp_mul_exp | (intros; apply GlobalTheory.DetExpP.det_half_one_add_exp_mul_exp <;> assumption)
