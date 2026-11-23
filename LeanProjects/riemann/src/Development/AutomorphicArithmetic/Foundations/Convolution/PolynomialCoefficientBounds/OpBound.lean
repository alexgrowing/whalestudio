import Mathlib

open MvPolynomial Filter Topology

private theorem UpperTheory.ConvolutionTheory.FX.opb_lin {Z V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (T : MvPolynomial Z ℂ →ₗ[ℂ] V) (P : MvPolynomial Z ℂ) (B : ℝ)
    (h : ∀ m ∈ P.support, ‖T (monomial m 1)‖ ≤ B) :
    ‖T P‖ ≤ (∑ α ∈ P.support, ‖P.coeff α‖) * B := by
  have e : T P = ∑ α ∈ P.support, P.coeff α • T (monomial α 1) := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← map_smul, smul_monomial, smul_eq_mul, mul_one]
  rw [e, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α hα => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (h α hα) (norm_nonneg _)

private theorem UpperTheory.ConvolutionTheory.FX.opb_deg {Z : Type} (P : MvPolynomial Z ℂ) (m : Z →₀ ℕ)
    (hm : m ∈ P.support) : m.degree ≤ P.totalDegree := by
  have := le_totalDegree hm
  simpa [Finsupp.degree_apply, Finsupp.sum] using this

private theorem UpperTheory.ConvolutionTheory.FX.opb_tail (x : ℝ) (hx : 0 ≤ x) (d e : ℕ) :
    ∑ k ∈ Finset.Ioc d e, x ^ k / k.factorial ≤ x ^ d / d.factorial * Real.exp x := by
  have h1 : ∑ k ∈ Finset.Ioc d e, x ^ k / (k.factorial : ℝ)
      ≤ ∑ k ∈ Finset.Ico d (e + 1), x ^ k / (k.factorial : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) (fun k _ _ => by positivity)
    simp only [Finset.mem_Ioc, Finset.mem_Ico] at hk ⊢
    omega
  refine h1.trans ?_
  rw [Finset.sum_Ico_eq_sum_range]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hx (e + 1 - d)) (by positivity))
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [div_mul_div_comm, pow_add]
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  have := Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add d j)
  exact_mod_cast this

theorem UpperTheory.ConvolutionTheory.FX.op_bound :
    ∀ (Z : Type) (Q : ℕ → MvPolynomial Z ℂ) (K₀ D : ℝ), 0 ≤ D → (∀ k, (Q k).totalDegree ≤ k) → (∀ k, (∑ α ∈ (Q k).support, ‖(Q k).coeff α‖) ≤ K₀ ^ (k + 1) / k.factorial) → ∃ C' : ℝ, 1 ≤ C' ∧
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (T : MvPolynomial Z ℂ →ₗ[ℂ] V) (K : ℝ), 0 ≤ K →
    ((∀ m : Z →₀ ℕ, ‖T (monomial m 1)‖ ≤ K * D ^ m.degree) → Summable (fun k => ‖T (Q k)‖) ∧ ∀ d e : ℕ, ‖∑ k ∈ Finset.Ioc d e, T (Q k)‖ ≤ K * C' ^ (d + 1) / d.factorial) ∧
    ∀ d : ℕ, (∀ m : Z →₀ ℕ, m.degree ≤ d → ‖T (monomial m 1)‖ ≤ K * D ^ d) → ‖∑ k ∈ Finset.range (d + 1), T (Q k)‖ ≤ K * C' ^ (d + 1) := by
  intro Z Q K₀ D hD hdeg hl
  have hK₀ : 0 ≤ K₀ := by
    have h := hl 0
    have h0 : 0 ≤ ∑ α ∈ (Q 0).support, ‖(Q 0).coeff α‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    simp only [zero_add, pow_one, Nat.factorial_zero, Nat.cast_one, div_one] at h
    exact h0.trans h
  set x : ℝ := K₀ * (D + 1) with hxdef
  have hx : 0 ≤ x := by positivity
  have hKx : K₀ ≤ x := by nlinarith [mul_nonneg hK₀ hD]
  have hE : 0 ≤ K₀ * Real.exp x := by positivity
  set C : ℝ := 1 + x + D + K₀ * Real.exp x with hC
  have hC1 : 1 ≤ C := by linarith
  have hCx : x ≤ C := by linarith
  have hCD : D ≤ C := by linarith
  have hCE : K₀ * Real.exp x ≤ C := by linarith
  refine ⟨C, hC1, fun V _ _ T K hK => ⟨fun hT => ?_, fun d hT => ?_⟩⟩
  · have hb : ∀ k, ‖T (Q k)‖ ≤ K * K₀ * (x ^ k / k.factorial) := by
      intro k
      have h1 := UpperTheory.ConvolutionTheory.FX.opb_lin T (Q k) (K * (D + 1) ^ k) (fun m hm => by
        refine (hT m).trans (mul_le_mul_of_nonneg_left ?_ hK)
        exact (pow_le_pow_left₀ hD (by linarith) _).trans
          (pow_le_pow_right₀ (by linarith) ((UpperTheory.ConvolutionTheory.FX.opb_deg _ m hm).trans (hdeg k))))
      refine h1.trans ((mul_le_mul_of_nonneg_right (hl k) (by positivity)).trans (le_of_eq ?_))
      rw [hxdef, mul_pow]; ring
    refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb
      ((Real.summable_pow_div_factorial x).mul_left _), fun d e => ?_⟩
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k _ => hb k).trans ?_)
    rw [← Finset.mul_sum]
    refine (mul_le_mul_of_nonneg_left (UpperTheory.ConvolutionTheory.FX.opb_tail x hx d e) (by positivity)).trans ?_
    have h2 : x ^ d * (K₀ * Real.exp x) ≤ C ^ (d + 1) := by
      rw [pow_succ]
      exact mul_le_mul (pow_le_pow_left₀ hx hCx d) hCE hE (by positivity)
    calc K * K₀ * (x ^ d / d.factorial * Real.exp x)
        = K * (x ^ d * (K₀ * Real.exp x)) / d.factorial := by ring
      _ ≤ K * C ^ (d + 1) / d.factorial := by gcongr
  · have hb : ∀ k ∈ Finset.range (d + 1), ‖T (Q k)‖ ≤ K * D ^ d * K₀ * (K₀ ^ k / k.factorial) := by
      intro k hk
      have hkd : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have h1 := UpperTheory.ConvolutionTheory.FX.opb_lin T (Q k) (K * D ^ d) (fun m hm =>
        hT m (((UpperTheory.ConvolutionTheory.FX.opb_deg _ m hm).trans (hdeg k)).trans hkd))
      refine h1.trans ((mul_le_mul_of_nonneg_right (hl k) (by positivity)).trans (le_of_eq ?_))
      ring
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hb).trans ?_)
    rw [← Finset.mul_sum]
    refine (mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hK₀ (d + 1)) (by positivity)).trans ?_
    have h3 : K₀ * Real.exp K₀ ≤ C :=
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hKx) hK₀).trans hCE
    have h2 : D ^ d * (K₀ * Real.exp K₀) ≤ C ^ (d + 1) := by
      rw [pow_succ]
      exact mul_le_mul (pow_le_pow_left₀ hD hCD d) h3 (by positivity) (by positivity)
    calc K * D ^ d * K₀ * Real.exp K₀ = K * (D ^ d * (K₀ * Real.exp K₀)) := by ring
      _ ≤ K * C ^ (d + 1) := by gcongr
