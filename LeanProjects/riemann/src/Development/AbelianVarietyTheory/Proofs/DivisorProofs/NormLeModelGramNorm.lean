import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.CurvInterp
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurvInterp

theorem modelWeight_bounds {ζ : ℂ} (h0 : ζ ≠ 0) (h1 : ‖ζ‖ < 1) :
    0 < ‖ζ‖ ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.tOf ζ ^ 2 ∧ ‖ζ‖ ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.tOf ζ ^ 2 ≤ 1 := by
  have hr : 0 < ‖ζ‖ := norm_pos_iff.2 h0
  have hlog : Real.log ‖ζ‖ < 0 := Real.log_neg hr h1
  have hpi : 0 < 2 * Real.pi := by positivity
  have ht : 0 < GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.tOf ζ := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.tOf; exact div_pos (by linarith) hpi
  refine ⟨by positivity, ?_⟩

  have hl : -Real.log ‖ζ‖ ≤ 1 / ‖ζ‖ - 1 := by
    have := Real.log_le_sub_one_of_pos (one_div_pos.2 hr)
    rw [one_div, Real.log_inv] at this; rwa [one_div]
  have hrt : ‖ζ‖ * GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.tOf ζ ≤ 1 := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.tOf
    rw [mul_div_assoc', div_le_one hpi]
    have : ‖ζ‖ * -Real.log ‖ζ‖ ≤ ‖ζ‖ * (1 / ‖ζ‖ - 1) := mul_le_mul_of_nonneg_left hl hr.le
    rw [mul_sub, mul_one_div_cancel hr.ne', mul_one] at this
    nlinarith [Real.pi_gt_three]
  have hpos : 0 ≤ ‖ζ‖ * GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.tOf ζ := by positivity
  calc ‖ζ‖ ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.tOf ζ ^ 2 = (‖ζ‖ * GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.tOf ζ) ^ 2 := by ring
    _ ≤ 1 := pow_le_one₀ hpos hrt

theorem norm_le_gnorm_modelGram : ∀ (e m : ℕ) (σ : Fin m → Option (Fin e)) (z : Fin e → ℂ),
    z ∈ punct σ (1 / 2) → ∀ ξ : Fin e → ℂ, ‖ξ‖ ≤ GlobalTheory.HermFrame.gnorm (modelGram σ z) ξ := by
  classical
  intro e m σ z hz ξ
  have hsq := GlobalTheory.HermFrame.gnorm_sq (modelGram_posSemidef σ z) ξ
  rw [form_modelGram, GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.modelAt] at hsq
  have hterm : ∀ k, ‖ξ k‖ ^ 2 ≤ (if ∃ i, σ i = some k then ‖ξ k‖ ^ 2 / (‖z k‖ ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.tOf (z k) ^ 2)
      else ‖ξ k‖ ^ 2) := by
    intro k
    split_ifs with hk
    · obtain ⟨i, hi⟩ := hk
      have hzk : ‖z k‖ < 1 := (norm_le_pi_norm z k).trans_lt
        ((mem_ball_zero_iff.1 hz.1).trans (by norm_num))
      obtain ⟨ha, hb⟩ := modelWeight_bounds (hz.2 i k hi) hzk
      exact le_div_self (sq_nonneg _) ha hb
    · exact le_rfl
  have hnn : ∀ k, 0 ≤ (if ∃ i, σ i = some k then ‖ξ k‖ ^ 2 / (‖z k‖ ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.tOf (z k) ^ 2)
      else ‖ξ k‖ ^ 2) := fun k => (sq_nonneg _).trans (hterm k)
  refine (pi_norm_le_iff_of_nonneg (GlobalTheory.HermFrame.gnorm_nonneg _ _)).2 fun k => ?_
  have hk2 : ‖ξ k‖ ^ 2 ≤ GlobalTheory.HermFrame.gnorm (modelGram σ z) ξ ^ 2 := by
    rw [hsq]
    exact (hterm k).trans (Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ k))
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (GlobalTheory.HermFrame.gnorm_nonneg _ _) two_ne_zero).1 hk2

end GlobalTheory.CurvInterp
