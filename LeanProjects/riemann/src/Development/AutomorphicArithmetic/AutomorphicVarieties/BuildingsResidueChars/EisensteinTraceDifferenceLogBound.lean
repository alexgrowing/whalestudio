import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CongruenceNumberRankThree
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.eisenstein_trace_difference_log_bound :
    ∀ (q e k : ℕ), 7 ≤ q → 1 ≤ e → 0 < k → ∀ z t : ℂ, z ^ k = 1 → ‖t‖ ≤ 3 → IsIntegral ℤ ((q : ℂ) ^ e * t) → t ≠ eis3 q e z ∧ IsIntegral ℤ ((q : ℂ) ^ e * (t - eis3 q e z)) ∧ Real.log ‖(q : ℂ) ^ e * (t - eis3 q e z)‖ ≤ 2 * e * Real.log q + 1 := by
  intro q e k hq he hk z t hz ht hI
  have hzn : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz hk.ne'
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hzn
  have hQN : 7 ≤ q ^ e := le_trans hq (Nat.le_self_pow (by omega) q)
  have hlogQ : Real.log ((q ^ e : ℕ) : ℝ) = e * Real.log q := by
    rw [Nat.cast_pow, Real.log_pow]
  have hcast : (q : ℂ) ^ e = ((q ^ e : ℕ) : ℂ) := by push_cast; rfl
  unfold eis3
  rw [hcast] at hI ⊢
  generalize q ^ e = N at hQN hlogQ hI
  have hN : (7 : ℝ) ≤ N := by exact_mod_cast hQN
  have hN0 : (N : ℂ) ≠ 0 := by
    have : N ≠ 0 := by omega
    exact_mod_cast this
  have hexp : (N : ℂ) * (t - ((N : ℂ)⁻¹ * z + 1 + (N : ℂ) * z⁻¹)) =
      (N : ℂ) * t - z - N - (N : ℂ) * N * z⁻¹ := by
    field_simp
    ring
  have hnA : ‖(N : ℂ) * t - z - N‖ ≤ 4 * N + 1 := by
    have h1 : ‖(N : ℂ) * t‖ ≤ 3 * N := by
      rw [norm_mul, Complex.norm_natCast]
      nlinarith
    have h2 := norm_sub_le ((N : ℂ) * t - z) (N : ℂ)
    have h3 := norm_sub_le ((N : ℂ) * t) z
    rw [Complex.norm_natCast] at h2
    linarith
  have hnB : ‖(N : ℂ) * N * z⁻¹‖ = N * N := by
    simp [hzn]
  have hne : (N : ℂ) * t - z - N - (N : ℂ) * N * z⁻¹ ≠ 0 := by
    intro h
    rw [sub_eq_zero.mp h, hnB] at hnA
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hne
    rw [← hexp, ← h, sub_self, mul_zero]
  · rw [hexp]
    have hzI : IsIntegral ℤ z := IsIntegral.of_pow hk (by rw [hz]; exact isIntegral_one)
    have hzI' : IsIntegral ℤ z⁻¹ :=
      IsIntegral.of_pow hk (by rw [inv_pow, hz, inv_one]; exact isIntegral_one)
    have hNI : IsIntegral ℤ (N : ℂ) := by
      have := isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (N : ℤ))
      simpa using this
    exact ((hI.sub hzI).sub hNI).sub ((hNI.mul hNI).mul hzI')
  · rw [hexp]
    have hb : ‖(N : ℂ) * t - z - N - (N : ℂ) * N * z⁻¹‖ ≤ 2 * ((N : ℝ) * N) := by
      have := norm_sub_le ((N : ℂ) * t - z - N) ((N : ℂ) * N * z⁻¹)
      nlinarith
    have hNpos : (0 : ℝ) < N := by linarith
    have h1 := Real.log_le_log (norm_pos_iff.mpr hne) hb
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul hNpos.ne' hNpos.ne', hlogQ] at h1
    have h2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
