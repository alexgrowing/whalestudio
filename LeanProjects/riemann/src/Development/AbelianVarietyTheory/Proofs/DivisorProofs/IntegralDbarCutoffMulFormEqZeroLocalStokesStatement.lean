import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDbarCutoffMulFormEqZeroLocalStokes
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_dbar_cutoff_mul_form_eq_zero_local_stokes : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (γ : A.Fld) (χ : M → ℝ) (i : A.ι), A.IsForm γ → A.SmoothOn univ (fun y => (χ y : ℂ)) → tsupport χ ⊆ (A.e i).source → A.integral (A.dbar (A.fn χ * γ)) = 0 := by
  first | exact @GlobalTheory.CxForm.DbarLocStokes.integral_dbar_fn_mul_eq_zero | exact GlobalTheory.CxForm.DbarLocStokes.integral_dbar_fn_mul_eq_zero | (intros; apply GlobalTheory.CxForm.DbarLocStokes.integral_dbar_fn_mul_eq_zero <;> assumption)
