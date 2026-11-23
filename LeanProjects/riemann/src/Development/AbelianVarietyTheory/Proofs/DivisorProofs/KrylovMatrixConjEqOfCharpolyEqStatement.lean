import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrylovMatrixConjEqOfCharpolyEq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrylovApply
open Matrix Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.krylovMatrix_conj_eq_of_charpoly_eq : ∀ {F : Type} [Field F] {r : ℕ} (y y' : Matrix (Fin r) (Fin r) F) (e e' : Fin r → F), y.charpoly = y'.charpoly → IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y e).det → IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y' e').det → (GlobalTheory.LeviDesc.Krylov.krylov y e)⁻¹ * y * GlobalTheory.LeviDesc.Krylov.krylov y e = (GlobalTheory.LeviDesc.Krylov.krylov y' e')⁻¹ * y' * GlobalTheory.LeviDesc.Krylov.krylov y' e' := by
  first | exact @GlobalTheory.LeviDesc.Krylov.krylov_conj_eq_of_charpoly_eq | exact GlobalTheory.LeviDesc.Krylov.krylov_conj_eq_of_charpoly_eq | (intros; apply GlobalTheory.LeviDesc.Krylov.krylov_conj_eq_of_charpoly_eq <;> assumption)
