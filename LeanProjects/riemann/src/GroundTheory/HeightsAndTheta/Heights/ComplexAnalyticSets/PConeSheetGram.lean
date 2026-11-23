import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConeSheetGramLintegral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.LogIntegrableOnOfLogIntegrable
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeSheetArea
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

theorem gramVol_const_zero {e n : ℕ} (y : Fin e → ℂ) :
    gramVol (fun _ : Fin e → ℂ => (0 : Fin n → ℂ)) y = 0 := by
  unfold gramVol
  have hw : (Fin.cons 0 (fun _ => 0) : Fin (e + 1) → Fin n → ℂ) = 0 := by
    funext a
    refine Fin.cases ?_ (fun j => ?_) a <;> simp
  have h0 : (Matrix.of fun (_ _ : Fin (e + 1)) => (0 : ℂ)).det = 0 := Matrix.det_zero
  simp [hw, h0]

theorem succ_le_of_ringKrullDim_quotient {n e : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞)) : e + 1 ≤ n := by
  have h := ringKrullDim_quotient_le J
  rw [hdim, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
  exact_mod_cast h

theorem ConeSheetGram.proof (hL : ConeSheetGramLintegral.Statement) : ConeSheetGram.Statement := by
  intro n e h J ℓ A f hJ hdim hℓ hA hf
  obtain ⟨hb0, -⟩ := coordBall_mass (n := n) (m := e + 1) (succ_le_of_ringKrullDim_quotient J hdim)
  rw [mul_setIntegral_eq_of_lintegral (ν := volume) (fun y => IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y)
    (fun y x => WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y))
    (fun y x t => ‖t‖ ^ (2 * e) *
      gramVol (fun y' => (h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y') y)
    (fun y x t => mul_nonneg (pow_nonneg (norm_nonneg t) _) (gramVol_nonneg _ y))
    (fun y x => (continuous_norm.pow _).mul continuous_const)
    (by positivity) hb0.ne' (fun F hF => hL n e h J ℓ A F hJ hdim hℓ hA hF) hf]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  unfold sheetSum
  refine finsum_congr fun x => finsum_congr fun _ => ?_
  unfold sheetThrough
  split_ifs with hs
  · rfl
  · simp [gramVol_const_zero]

end

end GroundTheory.Heights₂.Heights
