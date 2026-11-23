import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjMono
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl

theorem integrable_exp_lin_sub_sq_norm_complex {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) :
    Integrable fun w : ℂ => Real.exp (r * ‖w‖ - c * ‖w‖ ^ 2 / 2) := by
  have hg : Integrable fun w : ℂ => Real.exp (-(c / 4) * ‖w‖ ^ 2) := by
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := ((c / 4 : ℝ) : ℂ))
      (by simp; linarith) 0 0).norm
    refine h.congr (Filter.Eventually.of_forall fun w => ?_)
    simp [Complex.norm_exp, ← Complex.ofReal_pow]
  refine (hg.const_mul (Real.exp (r ^ 2 / c))).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have key : r ^ 2 / c + -(c / 4) * ‖w‖ ^ 2 - (r * ‖w‖ - c * ‖w‖ ^ 2 / 2)
      = (r - c * ‖w‖ / 2) ^ 2 / c := by
    field_simp
    ring
  have : 0 ≤ (r - c * ‖w‖ / 2) ^ 2 / c := by positivity
  linarith

theorem integrable_exp_lin_sub_gq (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ) (hc : ∀ τ, 0 < c τ)
    (z₀ : VCx ι a b) :
    Integrable fun z : VCx ι a b => Real.exp ((∑ k : DVar ι a b,
      ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) - gq c z / 2) := by
  have key : ∀ z : VCx ι a b, Real.exp ((∑ k : DVar ι a b,
      ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) - gq c z / 2)
      = ∏ τ, ∏ i, ∏ j, Real.exp (‖(c τ : ℂ) * z₀ τ i j‖ * ‖z τ i j‖ - c τ * ‖z τ i j‖ ^ 2 / 2) := by
    intro z
    simp only [← Real.exp_sum, gq, DVar, Fintype.sum_prod_type, Finset.sum_div,
      ← Finset.sum_sub_distrib]
  simp_rw [key]
  refine Integrable.fintype_prod (f := fun τ (x : Fin b → Fin a → ℂ) =>
    ∏ i, ∏ j, Real.exp (‖(c τ : ℂ) * z₀ τ i j‖ * ‖x i j‖ - c τ * ‖x i j‖ ^ 2 / 2)) fun τ => ?_
  refine Integrable.fintype_prod (f := fun i (y : Fin a → ℂ) =>
    ∏ j, Real.exp (‖(c τ : ℂ) * z₀ τ i j‖ * ‖y j‖ - c τ * ‖y j‖ ^ 2 / 2)) fun i => ?_
  refine Integrable.fintype_prod (f := fun j (w : ℂ) =>
    Real.exp (‖(c τ : ℂ) * z₀ τ i j‖ * ‖w‖ - c τ * ‖w‖ ^ 2 / 2)) fun j => ?_
  exact integrable_exp_lin_sub_sq_norm_complex (hc τ) (norm_nonneg _)

end GlobalTheory.FockTransl

end
