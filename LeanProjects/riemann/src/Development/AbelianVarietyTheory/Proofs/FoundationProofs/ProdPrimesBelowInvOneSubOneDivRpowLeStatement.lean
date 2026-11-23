import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdPrimesBelowInvOneSubOneDivRpowLe
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_primesBelow_inv_one_sub_rpow_le : ∀ (s : ℝ), 0 < s → ∀ N : ℕ, ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹ ≤ 1 + 1 / s := by
  first | exact @GlobalTheory.prod_primesBelow_inv_one_sub_one_div_rpow_le | exact GlobalTheory.prod_primesBelow_inv_one_sub_one_div_rpow_le | (intros; apply GlobalTheory.prod_primesBelow_inv_one_sub_one_div_rpow_le <;> assumption)
