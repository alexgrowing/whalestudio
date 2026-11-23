import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.HaarExist

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QPK

theorem local_weil_representation : LocWeil := by
  intro G _ _ _ _ _ _ _ _ muG _ μ _ hinv β hβ hβ1 F hF
  have hFm : Measurable (fun p : G × G => F (p.1 * p.2)) := hF.comp measurable_mul
  have hin : Measurable (fun x => ∫⁻ s, F (s * x) ∂μ) := hFm.lintegral_prod_left'
  rw [lintegral_withDensity_eq_lintegral_mul _ hβ hin]
  simp only [Pi.mul_apply]
  have step1 : ∀ x, β x * ∫⁻ s, F (s * x) ∂μ = ∫⁻ s, β x * F (s * x) ∂μ := fun x =>
    (lintegral_const_mul (β x) (hF.comp (measurable_id.mul_const x))).symm
  simp_rw [step1]
  rw [lintegral_lintegral_swap (μ := muG) (ν := μ) (f := fun x s => β x * F (s * x))
    ((hβ.comp measurable_fst).mul (hF.comp (measurable_snd.mul measurable_fst))).aemeasurable]
  have step2 : ∀ s, ∫⁻ x, β x * F (s * x) ∂muG = ∫⁻ x, β (s⁻¹ * x) * F x ∂muG := by
    intro s
    have key := lintegral_mul_left_eq_self (μ := muG) (fun x => β (s⁻¹ * x) * F x) s
    simp only [inv_mul_cancel_left] at key
    exact key
  simp_rw [step2]
  rw [lintegral_lintegral_swap (μ := μ) (ν := muG) (f := fun s x => β (s⁻¹ * x) * F x)
    ((hβ.comp (measurable_fst.inv.mul measurable_snd)).mul (hF.comp measurable_snd)).aemeasurable]
  have step3 : ∀ x, ∫⁻ s, β (s⁻¹ * x) * F x ∂μ = F x := by
    intro x
    rw [lintegral_mul_const (F x) (f := fun s => β (s⁻¹ * x)) (hβ.comp (measurable_inv.mul_const x))]
    have hsym : ∫⁻ s, β (s⁻¹ * x) ∂μ = ∫⁻ s, β (s * x) ∂μ := by
      conv_rhs => rw [← hinv]
      rw [lintegral_map (f := fun s => β (s * x)) (hβ.comp (measurable_id.mul_const x)) measurable_inv]
    rw [hsym, hβ1 x, one_mul]
  simp_rw [step3]

end QPK
