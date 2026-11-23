import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOfUnitMulComulEqTmulSelf
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_of_isUnit_mul_comul_eq_tmul : ∀ (K H : Type) [Field K] [CommRing H] [HopfAlgebra K H] (c : H ⊗[K] H), IsUnit c → ∀ u : H, u ≠ 0 → c * Coalgebra.comul (R := K) u = u ⊗ₜ[K] u → IsUnit u := by
  first | exact @GlobalTheory.isUnit_of_unit_mul_comul_eq_tmul_self | exact GlobalTheory.isUnit_of_unit_mul_comul_eq_tmul_self | (intros; apply GlobalTheory.isUnit_of_unit_mul_comul_eq_tmul_self <;> assumption)
