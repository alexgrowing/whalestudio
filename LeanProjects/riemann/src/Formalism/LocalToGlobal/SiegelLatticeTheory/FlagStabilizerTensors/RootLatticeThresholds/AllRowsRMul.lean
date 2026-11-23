import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AllRowsOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RConvFExistsPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RowsBij

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.AllRowsRMul

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf

variable {D : D7} (X : HidaSetting D)

abbrev phi (x y : X.B.I.L2 X.B.μf X.B.fund) (c : X.B.I.Gf) : ℂ := ⟪x, X.B.R (1, c) y⟫_ℂ

theorem R_facts :
    (∀ a b : X.B.I.GA, X.B.R (a * b) = (X.B.R a).comp (X.B.R b)) ∧ (∀ a F, ‖X.B.R a F‖ = ‖F‖) ∧
      (∀ x y : X.B.I.L2 X.B.μf X.B.fund, StronglyMeasurable (phi X x y)) := by
  have : X.B.μf.IsHaarMeasure := X.B.haar
  have hU := Formalism.L2.SG.Closed.GfUnimod_holds X.B.I X.B.μf
  have hFR := Formalism.L2.SG.Pf.foldReady_holds X.B.I
  have := hFR.2.1
  have := hFR.2.2.2.1
  have : X.B.μf.IsMulRightInvariant := hU
  have : (X.B.I.muA X.B.μf).IsMulLeftInvariant := rr_muA_left X.B.I X.B.μf
  have : (X.B.I.muA X.B.μf).IsMulRightInvariant := rr_muA_right X.B.I X.B.μf
  have : SigmaFinite (X.B.I.muA X.B.μf) := rr_muA_sigmaFinite X.B.I X.B.μf
  have h1 := rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec
  have h2 := rr_IsReg_of X.B.I X.B.μf X.B.fund X.B.R X.B.R_spec
  refine ⟨fun a b => rr_mul h1 h2 a b, fun a F => rr_norm h1 h2 a F, fun x y => ?_⟩
  exact (rr_weak_meas h1 h2 x y).comp_measurable (measurable_const.prodMk measurable_id)

theorem phi_bound (x y : X.B.I.L2 X.B.μf X.B.fund) (c : X.B.I.Gf) : ‖phi X x y c‖ ≤ ‖x‖ * ‖y‖ := by
  have h := (R_facts X).2.1 (1, c) y
  calc ‖phi X x y c‖ ≤ ‖x‖ * ‖X.B.R (1, c) y‖ := norm_inner_le_norm _ _
    _ = ‖x‖ * ‖y‖ := by rw [h]

theorem isRConvF_conv {f g : X.B.I.Gf → ℂ} {T U : X.B.I.L2 X.B.μf X.B.fund →L[ℂ] X.B.I.L2 X.B.μf X.B.fund}
    (hf : X.B.I.IsRConvF X.B.μf X.B.fund X.B.R f T) (hg : X.B.I.IsRConvF X.B.μf X.B.fund X.B.R g U) :
    X.B.I.IsRConvF X.B.μf X.B.fund X.B.R (X.B.I.convF X.B.μf f g) (T.comp U) := by
  obtain ⟨hmul, -, hmeas⟩ := R_facts X
  have : X.B.μf.IsHaarMeasure := X.B.haar
  have : SecondCountableTopology X.B.I.Gf := rr_secondCountable X.B.I X.B.μf
  have hK : Integrable (fun p : X.B.I.Gf × X.B.I.Gf => f p.1 * g (p.1⁻¹ * p.2)) (X.B.μf.prod X.B.μf) := by
    have h0 : Integrable (fun q : X.B.I.Gf × X.B.I.Gf => f q.1 * g q.2) (X.B.μf.prod X.B.μf) := hf.1.mul_prod hg.1
    exact ((measurePreserving_prod_inv_mul X.B.μf X.B.μf).integrable_comp h0.aestronglyMeasurable).2 h0
  have hF : ∀ x y : X.B.I.L2 X.B.μf X.B.fund, Integrable (fun p : X.B.I.Gf × X.B.I.Gf =>
      f p.1 * g (p.1⁻¹ * p.2) * phi X x y p.2) (X.B.μf.prod X.B.μf) := fun x y =>
    hK.mul_bdd ((hmeas x y).comp_measurable measurable_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => phi_bound X x y p.2)
  refine ⟨hK.integral_prod_right, fun x y => ?_⟩
  have step : ∀ a, ⟪x, X.B.R (1, a) (U y)⟫_ℂ = ∫ c, g (a⁻¹ * c) * phi X x y c ∂X.B.μf := by
    intro a
    rw [← ContinuousLinearMap.adjoint_inner_left, hg.2]
    have e : ∀ b, g b * ⟪ContinuousLinearMap.adjoint (X.B.R (1, a)) x, X.B.R (1, b) y⟫_ℂ =
        g b * phi X x y (a * b) := by
      intro b
      rw [ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply, ← hmul, Prod.mk_mul_mk, one_mul]
    simp_rw [e]
    rw [← integral_mul_left_eq_self (fun c => g (a⁻¹ * c) * phi X x y c) a]
    congr 1
    funext b
    simp only [inv_mul_cancel_left]
  rw [ContinuousLinearMap.comp_apply, hf.2]
  simp_rw [step, ← integral_const_mul]
  have hF' : Integrable (Function.uncurry fun a c => f a * (g (a⁻¹ * c) * phi X x y c)) (X.B.μf.prod X.B.μf) := by
    have := hF x y
    simp only [mul_assoc] at this
    exact this
  rw [integral_integral_swap hF']
  congr 1
  funext c
  unfold AutInst.convF
  rw [← integral_mul_const]
  congr 1
  funext a
  ring

end Formalism.L2.SG.Pf.AllRowsRMul
