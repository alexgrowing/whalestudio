import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization ComplexConjugate Matrix ENNReal
open MeasureTheory Set MvPolynomial

noncomputable section

namespace FSInv

open CP

private lemma measurable_lineOf' {N : ℕ} : Measurable (lineOf (N := N)) := by
  refine measurable_of_continuousOn_compl_singleton 0 ?_
  rw [continuousOn_iff_continuous_domRestrict]
  have h : ({0}ᶜ : Set (Fin (N + 1) → ℂ)).domRestrict lineOf =
      fun v => Projectivization.mk' ℂ ⟨v.1, v.2⟩ := by
    funext ⟨v, hv⟩; exact lineOf_of_ne hv
  rw [h]
  exact ProjTopology.continuous_mk'.comp (continuous_subtype_val.subtype_mk _)

private lemma chart_eq (hA : AmbChart.Statement) {N : ℕ} (i : Fin (N + 1)) :
    (fsChartMeasure i).map (chartInv i) =
      ENNReal.ofReal ((N + 1).factorial / Real.pi ^ (N + 1)) • (ambMeasure N).map lineOf := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf (measurable_chartInv i), fsChartMeasure,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_fsVolumeDensity i).ennreal_ofReal
      (g := fun z => f (chartInv i z)) (hf.comp (measurable_chartInv i)),
    lintegral_smul_measure, lintegral_map hf measurable_lineOf', hA N i f hf, smul_eq_mul,
    ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun z => ?_
  simp only [Pi.mul_apply]
  have hr : fsVolumeDensity (N := N) i z = ((N + 1).factorial / Real.pi ^ (N + 1) *
      (Real.pi / (N + 1))) * (1 / (1 + normSqSum z) ^ (N + 1)) := by
    rw [fsVolumeDensity_eq, Nat.factorial_succ]
    push_cast
    have := Real.pi_pos
    have := one_add_normSqSum_pos z
    field_simp
    ring
  rw [hr, ENNReal.ofReal_mul (by positivity)]
  ring

theorem AmbEq.proof (hA : AmbChart.Statement) : AmbEq.Statement := fun _ => chart_eq hA 0

end FSInv

end

end GroundTheory.Heights₂.Heights
