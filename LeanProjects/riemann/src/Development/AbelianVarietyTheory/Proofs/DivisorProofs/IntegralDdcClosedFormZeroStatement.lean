import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDdcClosedFormZero
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_ddc_closed_form_zero : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M]
    [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (η Z : A.Fld), A.IsForm η → A.IsForm Z → A.del Z = 0 →
    A.dbar Z = 0 → A.integral (A.ddc η * Z) = 0 := by
  first | exact @GlobalTheory.CxFormStokes.integral_ddc_mul_eq_zero | exact GlobalTheory.CxFormStokes.integral_ddc_mul_eq_zero | (intros; apply GlobalTheory.CxFormStokes.integral_ddc_mul_eq_zero <;> assumption)
