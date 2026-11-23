import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralAbsDetCpowBoundedShellEntire
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormRsHatLeConst
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIntegralUpperMspan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousIntegralOfCompact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralRsHatZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_absDet_cpow_bounded_shell_entire : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) (S : Set (GA E a)), NullMeasurableSet S μ → μ S < ⊤ → ∀ c : ℝ, 0 < c → (∀ g ∈ S, c ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1) → ∀ F : GA E a → ℂ, Continuous F → ∀ C : ℝ, (∀ g, ‖F g‖ ≤ C) → Differentiable ℂ fun s : ℂ => ∫ g in S, F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ := by
  first | exact @GlobalTheory.DiffInt.integral_absDet_cpow_entire | exact GlobalTheory.DiffInt.integral_absDet_cpow_entire | (intros; apply GlobalTheory.DiffInt.integral_absDet_cpow_entire; all_goals assumption)
