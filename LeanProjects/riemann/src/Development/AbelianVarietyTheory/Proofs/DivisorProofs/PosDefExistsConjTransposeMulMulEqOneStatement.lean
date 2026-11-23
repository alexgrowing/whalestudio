import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDefExistsConjTransposeMulMulEqOne
import Mathlib
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.posDef_exists_conjTranspose_mul_mul_eq_one' : ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) ℂ), H.PosDef → ∃ y₀ : GL (Fin d) ℂ, (y₀.1).conjTranspose * H * y₀.1 = 1 := by
  first | exact @GlobalTheory.posDef_exists_conjTranspose_mul_mul_eq_one | exact GlobalTheory.posDef_exists_conjTranspose_mul_mul_eq_one | (intros; apply GlobalTheory.posDef_exists_conjTranspose_mul_mul_eq_one <;> assumption)
