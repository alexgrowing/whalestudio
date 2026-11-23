import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open UpperHalfPlane hiding I
open scoped MatrixGroups

namespace UpperTheory.V.Af.Rs

private lemma nsq_eq (x : Fin 2 → ℤ) (z : ℍ) :
    Complex.normSq ((x 0 : ℂ) * z + (x 1 : ℂ)) =
      ((x 0 : ℝ) * z.re + x 1) ^ 2 + ((x 0 : ℝ) * z.im) ^ 2 := by
  simp [Complex.normSq_apply]; ring

private lemma nsq_pos (x : Fin 2 → ℤ) (hx : x ≠ 0) (z : ℍ) :
    0 < Complex.normSq ((x 0 : ℂ) * z + (x 1 : ℂ)) := by
  rw [nsq_eq]
  by_cases h0 : x 0 = 0
  · have h1 : x 1 ≠ 0 := by
      intro h1
      apply hx
      funext i
      fin_cases i
      · exact h0
      · exact h1
    have : (x 1 : ℝ) ≠ 0 := by exact_mod_cast h1
    simp only [h0, Int.cast_zero, zero_mul, zero_add]
    positivity
  · have : (x 0 : ℝ) ≠ 0 := by exact_mod_cast h0
    have := z.im_pos.ne'
    positivity

private lemma nsq_low (x : Fin 2 → ℤ) (z : ℍ) (hz : z ∈ ModularGroup.fd) :
    ‖x‖ ^ 2 ≤ 2 * Complex.normSq ((x 0 : ℂ) * z + (x 1 : ℂ)) := by
  rw [nsq_eq]
  obtain ⟨hz1, hzre⟩ := hz
  have hN : 1 ≤ z.re ^ 2 + z.im ^ 2 := by
    have := hz1
    rw [Complex.normSq_apply] at this
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at this
    nlinarith
  set a : ℝ := (x 0 : ℝ)
  set b : ℝ := (x 1 : ℝ)
  have hnorm : ‖x‖ ≤ max |a| |b| := by
    refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (abs_nonneg a))).mpr fun i => ?_
    fin_cases i
    · simp [Int.norm_eq_abs, a]
    · simp [Int.norm_eq_abs, b]
  have hM : (max |a| |b|) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    rcases le_total |a| |b| with h | h
    · rw [max_eq_right h, sq_abs]
      nlinarith [sq_nonneg a]
    · rw [max_eq_left h, sq_abs]
      nlinarith [sq_nonneg b]
  have hx2 : ‖x‖ ^ 2 ≤ (max |a| |b|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hab : -(|a| * |b|) ≤ 2 * a * b * z.re := by
    have h1 : |2 * a * b * z.re| ≤ |a| * |b| := by
      rw [abs_mul, abs_mul, abs_mul, abs_two]
      have := abs_nonneg a
      have := abs_nonneg b
      nlinarith [mul_nonneg (abs_nonneg a) (abs_nonneg b)]
    exact (abs_le.mp h1).1
  have hsq : a ^ 2 + b ^ 2 ≤ 2 * (a ^ 2 - |a| * |b| + b ^ 2) := by
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  have hexp : (a * z.re + b) ^ 2 + (a * z.im) ^ 2
      = a ^ 2 * (z.re ^ 2 + z.im ^ 2) + 2 * a * b * z.re + b ^ 2 := by ring
  rw [hexp]
  have : a ^ 2 ≤ a ^ 2 * (z.re ^ 2 + z.im ^ 2) := by
    nlinarith [sq_nonneg a]
  linarith

end UpperTheory.V.Af.Rs

theorem UpperTheory.V.Af.Rs.kerBd :
    UpperTheory.V.Af.Rs.KerBd := by
  intro s hs
  obtain ⟨hs1, hs2⟩ := hs
  have hs0 : 0 < s := by linarith
  have hzero : ∀ z, ker s 0 z = 0 := by
    intro z
    simp [ker, Real.zero_rpow hs0.ne']
  have hnn : ∀ (x : Fin 2 → ℤ) (z : ℍ), 0 ≤ z.im / Complex.normSq ((x 0 : ℂ) * z + (x 1 : ℂ)) :=
    fun x z => div_nonneg z.im_pos.le (Complex.normSq_nonneg _)
  refine ⟨?_, ?_, hzero, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x = 0
    · subst hx
      have : ker s 0 = fun _ => 0 := funext hzero
      rw [this]; exact continuous_const
    · unfold ker
      refine Continuous.rpow_const ?_ (fun _ => Or.inr hs0.le)
      refine Continuous.div UpperHalfPlane.continuous_im ?_ (fun z => (nsq_pos x hx z).ne')
      exact Complex.continuous_normSq.comp
        ((continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const)
  · intro x z
    exact Real.rpow_nonneg (hnn x z) _
  · intro γ z
    rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply]
    rfl
  · intro n x z
    have h : Complex.normSq (((((n : ℤ) • x) 0 : ℤ) : ℂ) * z + ((((n : ℤ) • x) 1 : ℤ) : ℂ)) =
        Complex.normSq ((x 0 : ℂ) * z + (x 1 : ℂ)) * (n : ℝ) ^ (2 : ℝ) := by
      rw [nsq_eq, nsq_eq]
      simp
      ring
    unfold ker
    rw [h, ← div_div, Real.div_rpow (hnn x z) (by positivity), ← Real.rpow_mul (Nat.cast_nonneg n)]
  · intro x z hz
    by_cases hx : x = 0
    · subst hx
      rw [hzero]
      positivity
    · have hp := nsq_pos x hx z
      have hl := nsq_low x z hz
      have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hy := z.im_pos
      have hy1 : 1 ≤ 2 * z.im := by
        have := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
        nlinarith
      have h1 : z.im / Complex.normSq ((x 0 : ℂ) * z + (x 1 : ℂ)) ≤ 2 * z.im / ‖x‖ ^ (2 : ℝ) := by
        rw [Real.rpow_two, div_le_div_iff₀ hp (by positivity)]
        nlinarith
      calc ker s x z ≤ (2 * z.im / ‖x‖ ^ (2 : ℝ)) ^ s := Real.rpow_le_rpow (hnn x z) h1 hs0.le
        _ = (2 * z.im) ^ s * ‖x‖ ^ (-(2 * s)) := by
          rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_mul hn.le,
            Real.rpow_neg hn.le, div_eq_mul_inv]
        _ ≤ (2 * z.im) ^ (2 : ℝ) * ‖x‖ ^ (-(2 * s)) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hy1 hs2) (by positivity)
        _ = _ := by rw [Real.rpow_two]; ring
