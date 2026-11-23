import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.JSW.WhitCont

open GroundTheory.Automorphic.FourierWhittaker

theorem continuous_whit : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (F : GA E a → ℂ), Continuous F →
    (∃ C : ℝ, ∀ g, ‖F g‖ ≤ C) → Continuous (GlobalTheory.JSW.whit F) := by
  intro E _ _ a F hF ⟨C, hC⟩
  set μ := (vecMeasure E (Pos a)).restrict (vecDomain E (Pos a)) with hμ
  haveI : IsFiniteMeasure μ :=
    ⟨by rw [hμ, Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  have hψ : Continuous fun X : Pos a → Ad E => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
    continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum 0).neg)
  have hj : Continuous fun p : GA E a × (Pos a → Ad E) =>
      F (uGL p.2 * p.1) * (GroundTheory.Global.adelicChar E (-supSum 0 p.2) : ℂ) :=
    (hF.comp ((continuous_uGL.comp continuous_snd).mul continuous_fst)).mul (hψ.comp continuous_snd)
  have e : GlobalTheory.JSW.whit F = fun g => ∫ X, F (uGL X * g) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) ∂μ := rfl
  rw [e]
  refine continuous_of_dominated (bound := fun _ => C) (fun g => ?_) (fun g => ?_) (integrable_const C) ?_
  · have h1 : Continuous fun X : Pos a → Ad E => (g, X) := continuous_const.prodMk continuous_id
    exact (hj.comp h1).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun X => ?_
    rw [norm_mul, Circle.norm_coe, mul_one]
    exact hC _
  · refine Filter.Eventually.of_forall fun X => ?_
    exact (hF.comp (continuous_const.mul continuous_id)).mul continuous_const

end GlobalTheory.JSW.WhitCont
