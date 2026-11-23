import Mathlib

noncomputable section

open MeasureTheory Complex

namespace PositivityTheory.SiegelWeilFormula.KLI

theorem intg_pow_quad {b : ℂ} (hb : b.re < 0) (k : ℕ) (c : ℂ) :
    Integrable (fun x : ℝ => (x : ℂ) ^ k * cexp (b * (x : ℂ) ^ 2 + c * x)) := by
  have h1 := (integrable_cexp_quadratic' hb (c + 1) 0).norm
  have h2 := (integrable_cexp_quadratic' hb (c - 1) 0).norm
  refine Integrable.mono' ((h1.add h2).const_mul (k.factorial : ℝ)) ?_ ?_
  · exact Continuous.aestronglyMeasurable (by fun_prop)
  · refine Filter.Eventually.of_forall fun x => ?_
    have hk : |x| ^ k ≤ k.factorial * Real.exp |x| := by
      have := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) k
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < k.factorial)] at this
      linarith
    have he : Real.exp |x| ≤ Real.exp x + Real.exp (-x) := by
      rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith [Real.exp_pos x, Real.exp_pos (-x)]
    set E := Real.exp ((b * (x : ℂ) ^ 2 + c * x).re) with hE
    have r1 : ‖cexp (b * (x : ℂ) ^ 2 + (c + 1) * x + 0)‖ = E * Real.exp x := by
      rw [Complex.norm_exp, hE, ← Real.exp_add]; congr 1; simp [add_mul]; try ring
    have r2 : ‖cexp (b * (x : ℂ) ^ 2 + (c - 1) * x + 0)‖ = E * Real.exp (-x) := by
      rw [Complex.norm_exp, hE, ← Real.exp_add]; congr 1; simp [sub_mul]; try ring
    have r0 : ‖(x : ℂ) ^ k * cexp (b * (x : ℂ) ^ 2 + c * x)‖ = |x| ^ k * E := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    simp only [Pi.add_apply]
    rw [r0, r1, r2]
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    calc |x| ^ k * E ≤ (k.factorial * Real.exp |x|) * E := mul_le_mul_of_nonneg_right hk hE0
      _ ≤ (k.factorial * (Real.exp x + Real.exp (-x))) * E := by gcongr
      _ = k.factorial * (E * Real.exp x + E * Real.exp (-x)) := by ring

def pk (b : ℂ) : ℕ → Polynomial ℂ
  | 0 => 1
  | 1 => Polynomial.C (-(2 * b)⁻¹) * Polynomial.X
  | (k + 2) => Polynomial.C (-(2 * b)⁻¹) * (Polynomial.X * pk b (k + 1) + Polynomial.C ((k + 1 : ℕ) : ℂ) * pk b k)

theorem pk_deg (b : ℂ) : ∀ k, (pk b k).natDegree ≤ k
  | 0 => by simp [pk]
  | 1 => by
    simp only [pk]
    exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
  | (k + 2) => by
    simp only [pk]
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine Polynomial.natDegree_mul_le.trans ?_
      have := pk_deg b (k + 1)
      have := (Polynomial.natDegree_X_le (R := ℂ))
      omega
    · exact (Polynomial.natDegree_C_mul_le _ _).trans ((pk_deg b k).trans (by omega))

def J (b : ℂ) (k : ℕ) (c : ℂ) : ℂ := ∫ x : ℝ, (x : ℂ) ^ k * cexp (b * (x : ℂ) ^ 2 + c * x)

theorem J_ibp {b : ℂ} (hb : b.re < 0) (k : ℕ) (c : ℂ) :
    2 * b * J b (k + 1) c + c * J b k c = -((k : ℂ) * J b (k - 1) c) := by
  have hu : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (y : ℂ) ^ k) ((k : ℂ) * (x : ℂ) ^ (k - 1)) x := fun x =>
    (hasDerivAt_pow k (x : ℂ)).comp_ofReal
  have hv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => cexp (b * (y : ℂ) ^ 2 + c * y))
      (cexp (b * (x : ℂ) ^ 2 + c * x) * (b * (2 * (x : ℂ)) + c)) x := by
    intro x
    have h0 : HasDerivAt (fun y : ℂ => b * y ^ 2 + c * y) (b * (2 * (x : ℂ)) + c) (x : ℂ) := by
      have h := ((hasDerivAt_pow 2 (x : ℂ)).const_mul b).add ((hasDerivAt_id (x : ℂ)).const_mul c)
      have e : b * (((2 : ℕ) : ℂ) * (x : ℂ) ^ (2 - 1)) + c * 1 = b * (2 * (x : ℂ)) + c := by push_cast; ring
      rw [e] at h
      exact h
    exact h0.comp_ofReal.cexp
  have I1 := intg_pow_quad hb (k + 1) c
  have I0 := intg_pow_quad hb k c
  have Im := intg_pow_quad hb (k - 1) c
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun y : ℝ => (y : ℂ) ^ k)
    (v := fun y : ℝ => cexp (b * (y : ℂ) ^ 2 + c * y))
    (u' := fun x : ℝ => (k : ℂ) * (x : ℂ) ^ (k - 1))
    (v' := fun x : ℝ => cexp (b * (x : ℂ) ^ 2 + c * x) * (b * (2 * (x : ℂ)) + c))
    (fun x _ => hu x) (fun x _ => hv x) ?_ ?_ I0
  · have e1 : ∀ x : ℝ, (x : ℂ) ^ k * (cexp (b * (x : ℂ) ^ 2 + c * x) * (b * (2 * (x : ℂ)) + c)) =
        (2 * b) * ((x : ℂ) ^ (k + 1) * cexp (b * (x : ℂ) ^ 2 + c * x)) +
          c * ((x : ℂ) ^ k * cexp (b * (x : ℂ) ^ 2 + c * x)) := fun x => by ring
    have e2 : ∀ x : ℝ, (k : ℂ) * (x : ℂ) ^ (k - 1) * cexp (b * (x : ℂ) ^ 2 + c * x) =
        (k : ℂ) * ((x : ℂ) ^ (k - 1) * cexp (b * (x : ℂ) ^ 2 + c * x)) := fun x => by ring
    beta_reduce at key
    simp_rw [e1, e2] at key
    rw [integral_add (I1.const_mul _) (I0.const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul] at key
    simpa [J] using key
  · have : (fun y : ℝ => (y : ℂ) ^ k) * (fun x : ℝ => cexp (b * (x : ℂ) ^ 2 + c * x) * (b * (2 * (x : ℂ)) + c)) =
        fun x : ℝ => (2 * b) * ((x : ℂ) ^ (k + 1) * cexp (b * (x : ℂ) ^ 2 + c * x)) +
          c * ((x : ℂ) ^ k * cexp (b * (x : ℂ) ^ 2 + c * x)) := by
      funext x; simp only [Pi.mul_apply]; ring
    rw [this]; exact (I1.const_mul _).add (I0.const_mul _)
  · have : (fun x : ℝ => (k : ℂ) * (x : ℂ) ^ (k - 1)) * (fun y : ℝ => cexp (b * (y : ℂ) ^ 2 + c * y)) =
        fun x : ℝ => (k : ℂ) * ((x : ℂ) ^ (k - 1) * cexp (b * (x : ℂ) ^ 2 + c * x)) := by
      funext x; simp only [Pi.mul_apply]; ring
    rw [this]; exact Im.const_mul _

theorem J_eq {b : ℂ} (hb : b.re < 0) : ∀ k c, J b k c = (pk b k).eval c * J b 0 c := by
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have h2b : (2 * b) ≠ 0 := mul_ne_zero two_ne_zero hb0
  have two : ∀ k, (∀ c, J b k c = (pk b k).eval c * J b 0 c) ∧ (∀ c, J b (k + 1) c = (pk b (k + 1)).eval c * J b 0 c) := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun c => by simp [pk], fun c => ?_⟩
      have := J_ibp hb 0 c
      simp only [CharP.cast_eq_zero, zero_mul, neg_zero] at this
      simp only [pk, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      field_simp
      linear_combination this
    | succ k ih =>
      refine ⟨ih.2, fun c => ?_⟩
      have := J_ibp hb (k + 1) c
      simp only [Nat.add_sub_cancel] at this
      rw [ih.2 c, ih.1 c] at this
      simp only [pk, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_add]
      field_simp
      push_cast at this ⊢
      linear_combination this
  exact fun k => (two k).1

theorem J_zero {b : ℂ} (hb : b.re < 0) (c : ℂ) :
    J b 0 c = (Real.pi / -b) ^ (1 / 2 : ℂ) * cexp (-(c ^ 2 / (4 * b))) := by
  have := integral_cexp_quadratic hb c 0
  simp only [add_zero, zero_sub] at this
  simpa [J] using this

end PositivityTheory.SiegelWeilFormula.KLI

end
