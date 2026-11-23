import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReLePowMulDetRe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_re_le_pow_mul_det_re_of_posDef : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) (κ : ℝ), A.PosDef → B.PosDef → (∀ c : ι → ℂ, (star c ⬝ᵥ A *ᵥ c).re ≤ κ * (star c ⬝ᵥ B *ᵥ c).re) → A.det.re ≤ κ ^ Fintype.card ι * B.det.re := by
  first | exact @GlobalTheory.HSAmp.det_re_le_pow_mul_det_re | exact GlobalTheory.HSAmp.det_re_le_pow_mul_det_re | (intros; apply GlobalTheory.HSAmp.det_re_le_pow_mul_det_re <;> assumption)
