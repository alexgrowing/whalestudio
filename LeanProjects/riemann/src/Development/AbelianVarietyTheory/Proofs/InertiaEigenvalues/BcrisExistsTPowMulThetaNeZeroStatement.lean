import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisExistsTPowMulThetaNeZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcris_exists_tPow_mul_theta_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (b : Per.Bcris l), b ≠ 0 → ∃ (m n : ℕ) (b' : Per.Bcris l) (y : Per.BdRp l), b * C.tB ^ m = C.tB ^ n * b' ∧ C.ι b' = algebraMap (Per.BdRp l) (Per.BdR l) y ∧ Per.θD l y ≠ 0 := by
  first | exact @GlobalTheory.MemLoc.RegDivide.exists_divide | exact GlobalTheory.MemLoc.RegDivide.exists_divide | (intros; apply GlobalTheory.MemLoc.RegDivide.exists_divide <;> assumption)
