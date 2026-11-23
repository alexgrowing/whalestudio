import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetPowerProductMulMemDelWShiftIff
import Mathlib
import Formalism.UnipotentAdelicQuotients.WeylLatDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFunApply
open GlobalTheory.IntegralityCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detPowerProduct_mul_mem_delW_shift_iff : ∀ (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ) (k : T → ℕ)
    (Φ : MvPolynomial (T × Fin N × Fin N) ℂ_[p]),
    ((fun y => (∏ τ, (y τ).det ^ k τ) * polFun Φ y) ∈ WeylLatticeDuality.DelW p T N (fun τ r => ν τ r + k τ) ↔
      polFun Φ ∈ WeylLatticeDuality.DelW p T N ν) := by
  first | exact @GlobalTheory.DetShiftWeyl.detPow_mul_mem_delW_iff | exact GlobalTheory.DetShiftWeyl.detPow_mul_mem_delW_iff | (intros; apply GlobalTheory.DetShiftWeyl.detPow_mul_mem_delW_iff <;> assumption)
