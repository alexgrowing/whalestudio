import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex

noncomputable section

open MeasureTheory Complex Set
open Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.WmFE

def jj (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := (g 1 1 : ℂ) - (g 1 0 : ℂ) * I

def nn (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := (g 0 1 : ℂ) - (g 0 0 : ℂ) * I

lemma range_val : range (Units.val : ℝˣ → ℝ) = {0}ᶜ := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact u.ne_zero
  · intro h
    exact ⟨Units.mk0 x h, rfl⟩

lemma measEmb_val : MeasurableEmbedding (Units.val : ℝˣ → ℝ) := by
  refine ⟨Units.val_injective, comap_measurable _, ?_⟩
  rintro s ⟨t, ht, rfl⟩
  rw [image_preimage_eq_inter_range, range_val]
  exact ht.inter (measurableSet_singleton 0).compl

lemma integral_mulR (f : ℝ → ℂ) :
    ∫ a : ℝˣ, f a ∂mulR = ∫ x in ({0}ᶜ : Set ℝ), ((|x|⁻¹ : ℝ) : ℂ) * f x := by
  have e := measEmb_val
  have hm : Measurable fun x : ℝ => ENNReal.ofReal |x|⁻¹ := by fun_prop
  unfold mulR
  rw [← e.integral_map, e.map_comap, range_val,
    restrict_withDensity (measurableSet_singleton 0).compl,
    integral_withDensity_eq_integral_toReal_smul hm (by simp)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (inv_nonneg.2 (abs_nonneg x))]

lemma integral_mulR_pos (f : ℝ → ℂ) (hf : ∀ x, x < 0 → f x = 0) :
    ∫ a : ℝˣ, f a ∂mulR = ∫ x in Ioi (0 : ℝ), (x : ℂ)⁻¹ * f x := by
  rw [integral_mulR]
  have hs : Ioi (0 : ℝ) ⊆ ({0}ᶜ : Set ℝ) := fun x hx => (ne_of_gt hx)
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero (measurableSet_singleton (0 : ℝ)).compl hs]
  · refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp [abs_of_pos (mem_Ioi.1 hx)]
  · rintro x ⟨h1, h2⟩
    have : x < 0 := lt_of_le_of_ne (not_lt.1 h2) h1
    simp [hf x this]

lemma integral_mulR_neg (f : ℝ → ℂ) (hf : ∀ x, 0 < x → f x = 0) :
    ∫ a : ℝˣ, f a ∂mulR = ∫ x in Ioi (0 : ℝ), (x : ℂ)⁻¹ * f (-x) := by
  rw [integral_mulR]
  have hs : Iio (0 : ℝ) ⊆ ({0}ᶜ : Set ℝ) := fun x hx => (ne_of_lt hx)
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero (measurableSet_singleton (0 : ℝ)).compl hs]
  · have h := integral_comp_neg_Ioi (0 : ℝ) (fun x : ℝ => ((|x|⁻¹ : ℝ) : ℂ) * f x)
    rw [neg_zero, integral_Iic_eq_integral_Iio] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp [abs_of_pos (mem_Ioi.1 hx)]
  · rintro x ⟨h1, h2⟩
    have : 0 < x := lt_of_le_of_ne (not_lt.1 h2) (Ne.symm h1)
    simp [hf x this]

lemma integral_mulR_eps (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (f : ℝ → ℂ) (hf : ∀ x, ε * x < 0 → f x = 0) :
    ∫ a : ℝˣ, f a ∂mulR = ∫ x in Ioi (0 : ℝ), (x : ℂ)⁻¹ * f (ε * x) := by
  rcases hε with rfl | rfl
  · simpa using integral_mulR_pos f (fun x hx => hf x (by simpa using hx))
  · simpa using integral_mulR_neg f (fun x hx => hf x (by simpa using hx))

lemma jj_ne {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) : jj g ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [jj] at h1 h2
  exact hg (by simp [Matrix.det_fin_two, h1, h2])

lemma real_whittaker_torus_mul (k : ℕ) (g : Matrix (Fin 2) (Fin 2) ℝ) (a : ℝ) (h : 0 < a * g.det) :
    Wm k (d2 a * g) = (((a * g.det) ^ ((2 * (k : ℝ) - 1) / 2) : ℝ) : ℂ) *
      (jj g) ^ (-(2 * (k : ℤ) - 1)) * Complex.exp (-2 * Real.pi * I * ((a : ℂ) * nn g / jj g)) := by
  have hdet : (d2 a * g).det = a * g.det := by
    rw [Matrix.det_mul]
    simp [d2, Matrix.det_fin_two_of]
  have e00 : (d2 a * g) 0 0 = a * g 0 0 := by simp [d2, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (d2 a * g) 0 1 = a * g 0 1 := by simp [d2, Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (d2 a * g) 1 0 = g 1 0 := by simp [d2, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (d2 a * g) 1 1 = g 1 1 := by simp [d2, Matrix.mul_apply, Fin.sum_univ_two]
  unfold Wm
  rw [hdet, if_pos h, e00, e01, e10, e11]
  simp only [jj, nn]
  push_cast
  congr 3
  ring

lemma real_whittaker_torus_mul_zero (k : ℕ) (g : Matrix (Fin 2) (Fin 2) ℝ) (a : ℝ) (h : ¬ 0 < a * g.det) :
    Wm k (d2 a * g) = 0 := by
  have hdet : (d2 a * g).det = a * g.det := by
    rw [Matrix.det_mul]
    simp [d2, Matrix.det_fin_two_of]
  unfold Wm
  rw [hdet, if_neg h]

lemma integrableOn_rpow_exp {σ b : ℝ} (hσ : -1 < σ) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ σ * Real.exp (-(b * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := σ) (p := 1) (b := b) hσ one_pos hb
  simpa [Real.rpow_one, neg_mul] using h

end GlobalTheory.CompanionTheory.WmFE
