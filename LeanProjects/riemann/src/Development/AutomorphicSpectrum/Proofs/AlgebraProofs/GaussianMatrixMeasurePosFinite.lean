import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PLeadBlockGaussTail

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix

open scoped ENNReal

noncomputable section

def entryGauss (z : ℂ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-‖z‖ ^ 2))

theorem measurable_entryGauss : Measurable entryGauss := by
  unfold entryGauss
  exact ENNReal.measurable_ofReal.comp
    (Real.continuous_exp.comp ((continuous_norm.pow 2).neg)).measurable

theorem lintegral_entryGauss_lt_top : ∫⁻ z, entryGauss z < ⊤ := by
  have hm : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (-x ^ 2)) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp ((continuous_pow 2).neg)).measurable
  have h1 : ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-x ^ 2)) < ⊤ := by
    simpa using (integrable_exp_neg_mul_sq one_pos).lintegral_lt_top
  have he : ∀ z : ℂ, entryGauss z =
      (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-p.1 ^ 2)) * ENNReal.ofReal (Real.exp (-p.2 ^ 2)))
        (Complex.measurableEquivRealProd z) := by
    intro z
    show ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) =
      ENNReal.ofReal (Real.exp (-z.re ^ 2)) * ENNReal.ofReal (Real.exp (-z.im ^ 2))
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]
    congr 2
    ring
  calc ∫⁻ z, entryGauss z
      = ∫⁻ z, (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-p.1 ^ 2)) * ENNReal.ofReal (Real.exp (-p.2 ^ 2)))
          (Complex.measurableEquivRealProd z) := lintegral_congr he
    _ = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Real.exp (-p.1 ^ 2)) * ENNReal.ofReal (Real.exp (-p.2 ^ 2)) :=
        Complex.volume_preserving_equiv_real_prod.lintegral_comp
          ((hm.comp measurable_fst).mul (hm.comp measurable_snd))
    _ = (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-x ^ 2))) * ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-x ^ 2)) := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod_mul hm.aemeasurable hm.aemeasurable
    _ < ⊤ := ENNReal.mul_lt_top h1 h1

theorem lintegral_entryGauss_pos : 0 < ∫⁻ z, entryGauss z := by
  rw [pos_iff_ne_zero, Ne, lintegral_eq_zero_iff measurable_entryGauss]
  intro h
  obtain ⟨z, hz⟩ := h.exists
  have : entryGauss z ≠ 0 := by
    simp [entryGauss, Real.exp_pos]
  exact this hz

theorem gaussM_univ_eq (m n : ℕ) :
    gaussM m n Set.univ = ∏ _i : Fin m, ∏ _j : Fin n, ∫⁻ z, entryGauss z := by
  have hx : ∀ x : Fin m → Fin n → ℂ, matGauss x = ∏ i, ∏ j, entryGauss (x i j) := by
    intro x
    simp only [matGauss, entryGauss, ← Finset.sum_neg_distrib, Real.exp_sum]
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => Finset.prod_nonneg fun j _ => (Real.exp_pos _).le)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le)]
  rw [gaussM, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simp_rw [hx]
  have hmeas : ∀ _i : Fin m, Measurable (fun y : Fin n → ℂ => ∏ j, entryGauss (y j)) := fun _ =>
    Finset.measurable_prod _ fun j _ => measurable_entryGauss.comp (measurable_pi_apply j)
  have hin : ∫⁻ y : Fin n → ℂ, ∏ j, entryGauss (y j) = ∏ _j : Fin n, ∫⁻ z, entryGauss z := by
    rw [volume_pi]
    exact LeadBlockGaussTail.lintegral_pi_prod (volume : Measure ℂ) n (fun _ => entryGauss)
      fun _ => measurable_entryGauss
  have hout := LeadBlockGaussTail.lintegral_pi_prod (volume : Measure (Fin n → ℂ)) m
    (fun _ y => ∏ j, entryGauss (y j)) hmeas
  rw [volume_pi]
  rw [hout]
  exact Finset.prod_congr rfl fun _ _ => hin

theorem gaussM_univ_pos_lt_top : ∀ m n : ℕ, 0 < gaussM m n Set.univ ∧ gaussM m n Set.univ < ⊤ := by
  intro m n
  rw [gaussM_univ_eq]
  constructor
  · exact CanonicallyOrderedAdd.prod_pos.2 fun i _ =>
      CanonicallyOrderedAdd.prod_pos.2 fun j _ => lintegral_entryGauss_pos
  · exact ENNReal.prod_lt_top fun i _ => ENNReal.prod_lt_top fun j _ => lintegral_entryGauss_lt_top

end

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
