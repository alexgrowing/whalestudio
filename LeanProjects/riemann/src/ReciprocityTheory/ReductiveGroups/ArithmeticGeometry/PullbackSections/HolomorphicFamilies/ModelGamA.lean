import Mathlib

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.MG

open Matrix

variable {r : ℕ}

def Eij (i j : Fin r) (s : ℂ) : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => if a = i ∧ b = j then s else 0

theorem mul_Eij (H : Matrix (Fin r) (Fin r) ℂ) (i j : Fin r) (s : ℂ) (a b : Fin r) :
    (H * Eij i j s) a b = if b = j then H a i * s else 0 := by
  simp only [Eij, Matrix.mul_apply, Matrix.of_apply]
  by_cases hb : b = j
  · subst hb
    simp [mul_ite]
  · simp [hb]

theorem Eij_mul (H : Matrix (Fin r) (Fin r) ℂ) (i j : Fin r) (s : ℂ) (a b : Fin r) :
    (Eij i j s * H) a b = if a = i then s * H j b else 0 := by
  simp only [Eij, Matrix.mul_apply, Matrix.of_apply]
  by_cases ha : a = i
  · subst ha
    simp [ite_mul]
  · simp [ha]

theorem Eij_sq (i j : Fin r) (hij : i ≠ j) (s : ℂ) : Eij i j s * Eij i j s = 0 := by
  ext a b
  rw [Eij_mul]
  simp [Eij, Ne.symm hij]

theorem unip_mul (i j : Fin r) (hij : i ≠ j) (s : ℂ) : (1 - Eij i j s) * (1 + Eij i j s) = 1 := by
  rw [sub_mul, one_mul, mul_add, mul_one, Eij_sq i j hij, add_zero, add_sub_cancel_right]

theorem det_unip (i j : Fin r) (hji : j < i) (s : ℂ) : (1 + Eij i j s).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp only [Matrix.add_apply, Matrix.one_apply_eq, Eij, Matrix.of_apply]
    rw [if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact lt_irrefl _ hji
  · intro a b hab
    have hab' : a < b := OrderDual.toDual_lt_toDual.mp hab
    simp only [Matrix.add_apply, Eij, Matrix.of_apply]
    rw [Matrix.one_apply_ne (ne_of_lt hab'), if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact lt_asymm hji hab'

theorem adj_unip (i j : Fin r) (hji : j < i) (s : ℂ) : adjugate (1 + Eij i j s) = 1 - Eij i j s := by
  have h1 : (1 + Eij i j s) * adjugate (1 + Eij i j s) = 1 := by
    rw [Matrix.mul_adjugate, det_unip i j hji, one_smul]
  calc adjugate (1 + Eij i j s)
      = ((1 - Eij i j s) * (1 + Eij i j s)) * adjugate (1 + Eij i j s) := by
        rw [unip_mul i j (ne_of_gt hji) s, one_mul]
    _ = 1 - Eij i j s := by rw [mul_assoc, h1, mul_one]

theorem conj_entry (H : Matrix (Fin r) (Fin r) ℂ) (i j : Fin r) (hij : i ≠ j) (s : ℂ) :
    ((1 - Eij i j s) * H * (1 + Eij i j s)) i j = H i j + s * (H i i - H j j) - s ^ 2 * H j i := by
  have h : (1 - Eij i j s) * H * (1 + Eij i j s) =
      H + H * Eij i j s - Eij i j s * H - Eij i j s * (H * Eij i j s) := by
    noncomm_ring
  rw [h]
  simp only [Matrix.add_apply, Matrix.sub_apply, mul_Eij, Eij_mul, if_true, ite_true, eq_self_iff_true]
  ring

theorem coeffs_of_small (a b c : ℂ) (δ : ℝ) (hδ : 0 < δ)
    (h : ∀ s : ℂ, ‖s‖ < δ → a + s * b - s ^ 2 * c = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have ha : a = 0 := by simpa using h 0 (by simpa using hδ)
  have htn : ‖((δ / 2 : ℝ) : ℂ)‖ = δ / 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have ht : ‖((δ / 2 : ℝ) : ℂ)‖ < δ := by rw [htn]; linarith
  have ht2 : ‖((δ / 2 : ℝ) : ℂ) / 2‖ < δ := by
    rw [norm_div, htn, Complex.norm_two]
    linarith
  have htne : ((δ / 2 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at htn
    linarith
  have h1 := h _ ht
  have h2 := h _ ht2
  rw [ha, zero_add] at h1 h2
  have e1 : b - ((δ / 2 : ℝ) : ℂ) * c = 0 := by
    have h3 : ((δ / 2 : ℝ) : ℂ) * (b - ((δ / 2 : ℝ) : ℂ) * c) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 htne
    · exact h4
  have e2 : b - ((δ / 2 : ℝ) : ℂ) / 2 * c = 0 := by
    have h3 : ((δ / 2 : ℝ) : ℂ) / 2 * (b - ((δ / 2 : ℝ) : ℂ) / 2 * c) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 (div_ne_zero htne two_ne_zero)
    · exact h4
  have hc : c = 0 := by
    have h3 : ((δ / 2 : ℝ) : ℂ) / 2 * c = 0 := by linear_combination e2 - e1
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 (div_ne_zero htne two_ne_zero)
    · exact h4
  refine ⟨ha, ?_, hc⟩
  linear_combination e1 + ((δ / 2 : ℝ) : ℂ) * hc

theorem scalar_of_small (H : Matrix (Fin r) (Fin r) ℂ)
    (h : ∀ i j : Fin r, j < i → ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℂ, ‖s‖ < δ →
      ((adjugate (1 + Eij i j s) * H * (1 + Eij i j s) : Matrix (Fin r) (Fin r) ℂ)) i j = 0) :
    ∀ i j : Fin r, (i ≠ j → H i j = 0) ∧ H i i = H j j := by
  have key : ∀ i j : Fin r, j < i → H i j = 0 ∧ H i i - H j j = 0 ∧ H j i = 0 := by
    intro i j hji
    obtain ⟨δ, hδ, hs⟩ := h i j hji
    apply coeffs_of_small (H i j) (H i i - H j j) (H j i) δ hδ
    intro s hs'
    have h1 := hs s hs'
    rwa [adj_unip i j hji, conj_entry H i j (ne_of_gt hji)] at h1
  intro i j
  constructor
  · intro hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact (key j i hlt).2.2
    · exact (key i j hgt).1
  · rcases lt_trichotomy i j with hlt | heq | hgt
    · exact (sub_eq_zero.mp (key j i hlt).2.1).symm
    · rw [heq]
    · exact sub_eq_zero.mp (key i j hgt).2.1

end ReciprocityTheory.ChartRestriction.G.PullbackSections.MG
