import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.StepBruhat

noncomputable section

open MeasureTheory Measure
open scoped ENNReal

namespace PI.WeilQuotMeas.UnitaryGroupMassFormula

theorem stepInvInv : StepInvInv := by
  intro K _ _ _ _ _ _ _ μ hμ hμr
  constructor
  let c : ℝ≥0∞ := haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := isMulLeftInvariant_eq_smul μ.inv μ
  have : map Inv.inv (map Inv.inv μ) = c ^ 2 • μ := by
    rw [← inv_def μ, hc, Measure.map_smul, ← inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [map_map continuous_inv.measurable continuous_inv.measurable] at this
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id]
  have P : TopologicalSpace.PositiveCompacts K := Classical.arbitrary _
  have : c ^ 2 * μ P = 1 ^ 2 * μ P := by
    conv_rhs => rw [μeq]
    simp
  have : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (measure_pos_of_nonempty_interior _ P.interior_nonempty).ne'
          P.isCompact.measure_lt_top.ne).1 this
  have : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective this
  rw [hc, this, one_smul]

end PI.WeilQuotMeas.UnitaryGroupMassFormula
