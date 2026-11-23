import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaMultiplicityWeight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd

open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.FSCrofton

theorem integral_exp_neg_norm_sq : ∫ z : ℂ, Real.exp (-‖z‖ ^ 2) = Real.pi := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) (b := 1) one_pos
  have hd : (Module.finrank ℝ ℂ : ℝ) / 2 = 1 := by simp [Complex.finrank_real_complex]
  simp only [one_mul, div_one, hd, Real.rpow_one, neg_mul] at h
  exact h

theorem lintegral_exp_neg_norm_sq :
    ∫⁻ z : ℂ, ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) = ENNReal.ofReal Real.pi := by
  have hi : Integrable (fun z : ℂ => Real.exp (-‖z‖ ^ 2)) := by
    by_contra hn
    have h0 := integral_undef hn
    rw [integral_exp_neg_norm_sq] at h0
    exact Real.pi_ne_zero h0
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le), integral_exp_neg_norm_sq]

theorem lintegral_gW (d : ℕ) (α : Type) [Fintype α] :
    ∫⁻ C : Fin d → α → ℂ, gW d α C = ENNReal.ofReal (Real.pi ^ (d * Fintype.card α)) := by
  have hw : ∀ C : Fin d → α → ℂ, gW d α C =
      ∏ k, ∏ j, ENNReal.ofReal (Real.exp (-‖C k j‖ ^ 2)) := by
    intro C
    unfold gW
    simp only [← Finset.sum_neg_distrib, Real.exp_sum]
    rw [ENNReal.ofReal_prod_of_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le]
    exact Finset.prod_congr rfl fun k _ =>
      ENNReal.ofReal_prod_of_nonneg fun _ _ => (Real.exp_pos _).le
  have hm : Measurable fun z : ℂ => ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) := by fun_prop
  have hrow : ∫⁻ r : α → ℂ, ∏ j, ENNReal.ofReal (Real.exp (-‖r j‖ ^ 2)) =
      ENNReal.ofReal Real.pi ^ Fintype.card α := by
    rw [volume_pi, GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod (fun _ => hm.aemeasurable)]
    simp [lintegral_exp_neg_norm_sq]
  have hmr : Measurable fun r : α → ℂ => ∏ j, ENNReal.ofReal (Real.exp (-‖r j‖ ^ 2)) :=
    Finset.measurable_prod _ fun j _ => hm.comp (measurable_pi_apply j)
  simp only [hw]
  rw [volume_pi, GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod (fun _ => hmr.aemeasurable)]
  simp only [hrow, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, mul_comm, ENNReal.ofReal_pow Real.pi_pos.le, mul_comm]

end GlobalTheory.CompanionTheory.FSCrofton
