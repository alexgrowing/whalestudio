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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MellinIntegralRapidDecayEntireOfLeOne
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

namespace GlobalTheory.DiffInt

theorem integral_absDet_cpow_entire : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) (S : Set (GA E a)), NullMeasurableSet S μ → μ S < ⊤ → ∀ c : ℝ, 0 < c → (∀ g ∈ S, c ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1) → ∀ F : GA E a → ℂ, Continuous F → ∀ C : ℝ, (∀ g, ‖F g‖ ≤ C) → Differentiable ℂ fun s : ℂ => ∫ g in S, F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ := by
  intro E _ _ _ a μ S hS hμS c hc hδ F hF C hC
  set δ : GA E a → ℝ := fun g => (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδdef
  have hδc : Continuous δ := GlobalTheory.RSThetaLow.continuous_absDet
  have hae : ∀ᵐ g ∂(μ.restrict S), g ∈ S := ae_restrict_mem₀ hS
  haveI : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hμS.ne
  have key := GlobalTheory.integral_mul_cpow_of_rapid_decay_entire (GA E a) (μ.restrict S) δ F hδc.measurable
    (hae.mono fun g hg => ⟨lt_of_lt_of_le hc (hδ g hg).1, (hδ g hg).2⟩)
    (by
      refine Integrable.mono' (integrable_const (1 : ℝ)) hδc.aestronglyMeasurable ?_
      refine hae.mono fun g hg => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hc.le (hδ g hg).1)]
      exact (hδ g hg).2)
    hF.aestronglyMeasurable
    (by
      intro K
      refine ⟨max C 0 / c ^ K, hae.mono fun g hg => ?_⟩
      have hcK : 0 < c ^ K := pow_pos hc K
      have h1 : c ^ K ≤ δ g ^ K := pow_le_pow_left₀ hc.le (hδ g hg).1 K
      rw [div_mul_eq_mul_div, le_div_iff₀ hcK]
      calc ‖F g‖ * c ^ K ≤ max C 0 * c ^ K :=
            mul_le_mul_of_nonneg_right ((hC g).trans (le_max_left _ _)) hcK.le
        _ ≤ max C 0 * δ g ^ K := mul_le_mul_of_nonneg_left h1 (le_max_right _ _))
  have := key.2.comp (differentiable_id.sub_const (1 : ℂ))
  exact this

end GlobalTheory.DiffInt
