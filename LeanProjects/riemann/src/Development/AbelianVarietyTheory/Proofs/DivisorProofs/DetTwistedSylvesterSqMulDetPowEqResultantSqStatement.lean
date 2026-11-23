import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetTwistedSylvesterSqMulDetPowEqResultantSq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_twistedSylvester_sq_mul_det_pow_eq_resultant_sq : ∀ (k : Type) [Field k] (a b : ℕ) (A : GL (Fin a) k) (B : Matrix (Fin b) (Fin b) k), LinearMap.det (GlobalTheory.LeviDesc.adL A B) ^ 2 * A.val.det ^ (2 * b) = resultant A.val.charpoly B.charpoly ^ 2 := by
  first | exact @GlobalTheory.LeviDesc.det_adL_sq_mul_det_pow | exact GlobalTheory.LeviDesc.det_adL_sq_mul_det_pow | (intros; apply GlobalTheory.LeviDesc.det_adL_sq_mul_det_pow <;> assumption)
