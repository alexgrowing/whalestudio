import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalOfInvMul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowTEqRowS
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_inv_mul_and_norm_inv_le_one : ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (m : Type) [Fintype m] [DecidableEq m] (N : ℕ) (B : ℕ → Matrix m m F), (∀ n i j, ‖B n i j‖ ≤ 1) → (∀ n, N < n → ∀ i j, ‖B n i j‖ < 1) → ‖(B N).det‖ = 1 → Normal N (fun n => (B N)⁻¹ * B n) ∧ ∀ i j, ‖(B N)⁻¹ i j‖ ≤ 1 := by
  first | exact @GlobalTheory.PMonE.normal_of_inv_mul | exact GlobalTheory.PMonE.normal_of_inv_mul | (intros; apply GlobalTheory.PMonE.normal_of_inv_mul <;> assumption)
