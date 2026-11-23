import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoConstPowMulPowPowZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
open PowerSeries GlobalTheory.BK Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_const_pow_mul_pow_pow_zero' : ∀ (C r : ℝ) (l : ℕ), 0 ≤ C → 0 ≤ r → r < 1 → 2 ≤ l → Tendsto (fun n : ℕ => C ^ n * r ^ (l ^ n)) atTop (𝓝 0) := by
  first | exact @GlobalTheory.tendsto_const_pow_mul_pow_pow_zero | exact GlobalTheory.tendsto_const_pow_mul_pow_pow_zero | (intros; apply GlobalTheory.tendsto_const_pow_mul_pow_pow_zero <;> assumption)
