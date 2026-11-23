import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.DdMemUnitary

noncomputable section

open Matrix

namespace PositivityTheory.KB.MomentRationality.Cz.Red

theorem local_decomp {ι : Type*} [Fintype ι] [Nonempty ι] {N : ℕ} (hN : 1 ≤ N) {M t : ℝ} (hM : 0 < M)
    (ht : 0 < t) {r : Fin N → ℝ} (hr : ∀ i, 0 < r i) (hrt : ∀ i j : Fin N, (j : ℕ) = i + 1 → t * r j ≤ r i)
    (a : ι → ℂ) (b k : ι → Matrix (Fin N) (Fin N) ℂ) (hb : ∀ w, (b w).BlockTriangular id)
    (hbM : ∀ w i j, ‖b w i j‖ ≤ M) (hbm : ∀ w i, M⁻¹ ≤ ‖b w i i‖)
    (hk : ∀ w, k w ∈ unitaryGroup (Fin N) ℂ)
    (hdet : ∀ w, (a w • (b w * diagonal (fun i => ((r i : ℝ) : ℂ)) * k w)).det = 1) :
    ∃ (p k' : ι → Matrix (Fin N) (Fin N) ℂ) (s : Fin N → ℝ), ∑ i, s i = 0 ∧
      (∀ i j : Fin N, (j : ℕ) = i + 1 → s j ≤ s i + (4 * Real.log M - Real.log t)) ∧
      (∀ w, (p w).BlockTriangular id) ∧ (∀ w i j, ‖p w i j‖ ≤ Real.exp (4 * Real.log M)) ∧
      (∀ w i, Real.exp (-(4 * Real.log M)) ≤ ‖p w i i‖) ∧ (∀ i, ∏ w, ‖p w i i‖ = 1) ∧
      (∀ w, (p w).det = 1) ∧ (∀ w, k' w ∈ unitaryGroup (Fin N) ℂ) ∧ (∀ w, (k' w).det = 1) ∧
      ∀ w, a w • (b w * diagonal (fun i => ((r i : ℝ) : ℂ)) * k w) =
        p w * diagonal (fun i => ((Real.exp (s i) : ℝ) : ℂ)) * k' w := by
  classical
  have hM1 : 1 ≤ M := by
    obtain ⟨w⟩ := ‹Nonempty ι›
    have h1 := hbM w ⟨0, hN⟩ ⟨0, hN⟩
    have h2 := hbm w ⟨0, hN⟩
    by_contra h
    push_neg at h
    have h3 : 1 < M⁻¹ := (one_lt_inv₀ hM).mpr h
    linarith
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hbpos : ∀ w i, 0 < ‖b w i i‖ := fun w i => lt_of_lt_of_le (inv_pos.mpr hM) (hbm w i)
  have hBle : ∀ w i, Real.log ‖b w i i‖ ≤ Real.log M := fun w i =>
    Real.log_le_log (hbpos w i) (hbM w i i)
  have hBge : ∀ w i, -Real.log M ≤ Real.log ‖b w i i‖ := by
    intro w i
    rw [← Real.log_inv]
    exact Real.log_le_log (inv_pos.mpr hM) (hbm w i)
  have hnorm : ∀ w, ‖a w‖ ^ N * ((∏ i, ‖b w i i‖) * ∏ i, r i) = 1 := by
    intro w
    have h := congrArg norm (hdet w)
    have hk1 : ‖(k w).det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary (hk w))
    rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_of_upperTriangular (hb w),
      Matrix.det_diagonal] at h
    simp only [norm_mul, norm_pow, norm_prod, Fintype.card_fin, hk1, mul_one, norm_one,
      Complex.norm_real, Real.norm_eq_abs] at h
    rw [Finset.prod_congr rfl (fun i _ => abs_of_pos (hr i))] at h
    simpa [mul_assoc] using h
  have hapos : ∀ w, 0 < ‖a w‖ := by
    intro w
    rcases (norm_nonneg (a w)).lt_or_eq with h | h
    · exact h
    · have h1 := hnorm w
      rw [← h, zero_pow (by omega), zero_mul] at h1
      exact absurd h1 zero_ne_one
  have hsumlog : ∀ w, (N : ℝ) * Real.log ‖a w‖ + ∑ i, Real.log ‖b w i i‖ + ∑ i, Real.log (r i) = 0 := by
    intro w
    have h := congrArg Real.log (hnorm w)
    rw [Real.log_one, Real.log_mul (pow_ne_zero _ (hapos w).ne')
      (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => (hbpos w i).ne')
        (Finset.prod_ne_zero_iff.mpr fun i _ => (hr i).ne')),
      Real.log_mul (Finset.prod_ne_zero_iff.mpr fun i _ => (hbpos w i).ne')
        (Finset.prod_ne_zero_iff.mpr fun i _ => (hr i).ne'),
      Real.log_pow, Real.log_prod (fun i _ => (hbpos w i).ne'),
      Real.log_prod (fun i _ => (hr i).ne')] at h
    linarith
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hdiff : ∀ w w', Real.log ‖a w‖ - Real.log ‖a w'‖ ≤ 2 * Real.log M := by
    intro w w'
    have h1 := hsumlog w
    have h2 := hsumlog w'
    have hle : ∑ i, (Real.log ‖b w' i i‖ - Real.log ‖b w i i‖) ≤ ∑ i : Fin N, 2 * Real.log M :=
      Finset.sum_le_sum (fun i _ => by linarith [hBle w' i, hBge w i])
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_sub_distrib] at hle
    have h3 : (N : ℝ) * (Real.log ‖a w‖ - Real.log ‖a w'‖) ≤ N * (2 * Real.log M) := by nlinarith
    exact le_of_mul_le_mul_left h3 hNpos
  have avg_le : ∀ (f : ι → ℝ) (c : ℝ), (∀ w, f w ≤ c) → (∑ w, f w) / Fintype.card ι ≤ c := by
    intro f c h
    rw [div_le_iff₀ hn]
    have := Finset.sum_le_sum (fun w (_ : w ∈ Finset.univ) => h w)
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using this
  have le_avg : ∀ (f : ι → ℝ) (c : ℝ), (∀ w, c ≤ f w) → c ≤ (∑ w, f w) / Fintype.card ι := by
    intro f c h
    rw [le_div_iff₀ hn]
    have := Finset.sum_le_sum (fun w (_ : w ∈ Finset.univ) => h w)
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using this
  obtain ⟨s, hs⟩ : ∃ s : Fin N → ℝ, s = fun j =>
      (∑ w, (Real.log ‖a w‖ + Real.log ‖b w j j‖)) / Fintype.card ι + Real.log (r j) := ⟨_, rfl⟩
  have hs_sum : ∑ j, s j = 0 := by
    have h1 : ∀ w, ∑ j, (Real.log ‖a w‖ + Real.log ‖b w j j‖) = -∑ j, Real.log (r j) := by
      intro w
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      linarith [hsumlog w]
    rw [hs]
    simp only
    rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_comm, Finset.sum_congr rfl (fun w _ => h1 w),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  have hs_step : ∀ i j : Fin N, (j : ℕ) = i + 1 → s j ≤ s i + (4 * Real.log M - Real.log t) := by
    intro i j hij
    have hr' : Real.log (r j) ≤ Real.log (r i) - Real.log t := by
      have h := Real.log_le_log (mul_pos ht (hr j)) (hrt i j hij)
      rw [Real.log_mul ht.ne' (hr j).ne'] at h
      linarith
    have hB : (∑ w, (Real.log ‖b w j j‖ - Real.log ‖b w i i‖)) / Fintype.card ι ≤ 2 * Real.log M :=
      avg_le _ _ (fun w => by linarith [hBle w j, hBge w i])
    have hsplit : ∑ w, (Real.log ‖b w j j‖ - Real.log ‖b w i i‖) =
        ∑ w, (Real.log ‖a w‖ + Real.log ‖b w j j‖) - ∑ w, (Real.log ‖a w‖ + Real.log ‖b w i i‖) := by
      rw [← Finset.sum_sub_distrib]
      congr 1
      funext w
      ring
    rw [hsplit, sub_div] at hB
    rw [hs]
    simp only
    linarith
  have he_up : ∀ w j, Real.log ‖a w‖ + Real.log (r j) - s j ≤ 3 * Real.log M := by
    intro w j
    have h : Real.log ‖a w‖ + Real.log (r j) - s j =
        (∑ w', (Real.log ‖a w‖ - Real.log ‖a w'‖ - Real.log ‖b w' j j‖)) / Fintype.card ι := by
      rw [hs]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      field_simp
      ring
    rw [h]
    exact avg_le _ _ (fun w' => by linarith [hdiff w w', hBge w' j])
  have hd_low : ∀ w i, -(4 * Real.log M) ≤
      Real.log ‖b w i i‖ + (Real.log ‖a w‖ + Real.log (r i) - s i) := by
    intro w i
    have h : Real.log ‖b w i i‖ + (Real.log ‖a w‖ + Real.log (r i) - s i) =
        (∑ w', (Real.log ‖a w‖ - Real.log ‖a w'‖ + Real.log ‖b w i i‖ - Real.log ‖b w' i i‖)) /
          Fintype.card ι := by
      rw [hs]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      field_simp
      ring
    rw [h]
    exact le_avg _ _ (fun w' => by linarith [hdiff w' w, hBge w i, hBle w' i])
  have hprod0 : ∀ i, ∑ w, (Real.log ‖b w i i‖ + (Real.log ‖a w‖ + Real.log (r i) - s i)) = 0 := by
    intro i
    rw [hs]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    field_simp
    ring
  have hz : ∀ w j, 0 < ‖a w * b w j j‖ := fun w j => by
    rw [norm_mul]
    exact mul_pos (hapos w) (hbpos w j)
  obtain ⟨φ, hφ⟩ : ∃ φ : ι → Fin N → ℂ, φ = fun w j =>
      (a w * b w j j) / ((‖a w * b w j j‖ : ℝ) : ℂ) := ⟨_, rfl⟩
  have hφnorm : ∀ w j, ‖φ w j‖ = 1 := by
    intro w j
    rw [hφ]
    simp only
    rw [norm_div, Complex.norm_real, norm_norm, div_self (hz w j).ne']
  have hφn : ∀ w j, star (φ w j) * φ w j = 1 := by
    intro w j
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hφnorm]
    simp
  have hφz : ∀ w j, a w * b w j j * star (φ w j) = ((‖a w * b w j j‖ : ℝ) : ℂ) := by
    intro w j
    have hne : ((‖a w * b w j j‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hz w j).ne'
    rw [hφ]
    simp only
    simp only [star_div₀, Complex.star_def, Complex.conj_ofReal]
    rw [← mul_div_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    field_simp
    push_cast
    ring
  obtain ⟨d, hd⟩ : ∃ d : ι → Fin N → ℂ, d = fun w j =>
      a w * ((r j * Real.exp (-s j) : ℝ) : ℂ) * star (φ w j) := ⟨_, rfl⟩
  have hdnorm : ∀ w j, ‖d w j‖ = Real.exp (Real.log ‖a w‖ + Real.log (r j) - s j) := by
    intro w j
    rw [hd]
    simp only
    rw [norm_mul, norm_mul, norm_star, hφnorm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (hr j) (Real.exp_pos _)), Real.exp_sub, Real.exp_add,
      Real.exp_log (hapos w), Real.exp_log (hr j), Real.exp_neg]
    field_simp
  have hpn : ∀ w i j, ‖(b w * diagonal (d w)) i j‖ =
      ‖b w i j‖ * Real.exp (Real.log ‖a w‖ + Real.log (r j) - s j) := by
    intro w i j
    rw [Matrix.mul_diagonal, norm_mul, hdnorm]
  have hpdiag : ∀ w i, ‖(b w * diagonal (d w)) i i‖ =
      Real.exp (Real.log ‖b w i i‖ + (Real.log ‖a w‖ + Real.log (r i) - s i)) := by
    intro w i
    rw [hpn, Real.exp_add, Real.exp_log (hbpos w i)]
  have hdetp : ∀ w, (b w * diagonal (d w)).det = 1 := by
    intro w
    rw [Matrix.det_mul, Matrix.det_of_upperTriangular (hb w), Matrix.det_diagonal,
      ← Finset.prod_mul_distrib]
    have h1 : ∀ j, b w j j * d w j = ((‖a w‖ * ‖b w j j‖ * (r j * Real.exp (-s j)) : ℝ) : ℂ) := by
      intro j
      rw [hd]
      simp only
      have h2 := hφz w j
      rw [norm_mul] at h2
      push_cast at h2 ⊢
      linear_combination ((r j : ℂ) * Complex.exp (-(s j : ℂ))) * h2
    rw [Finset.prod_congr rfl (fun j _ => h1 j), ← Complex.ofReal_prod]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← Real.exp_sum, Finset.sum_neg_distrib, hs_sum, neg_zero,
      Real.exp_zero, mul_one]
    rw [mul_assoc, hnorm w, Complex.ofReal_one]
  have hdiagu : ∀ w, diagonal (φ w) ∈ unitaryGroup (Fin N) ℂ := by
    intro w
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    rw [Pi.star_apply, mul_comm]
    exact hφn w j
  have hmain : ∀ w, a w • (b w * diagonal (fun i => ((r i : ℝ) : ℂ)) * k w) =
      b w * diagonal (d w) * diagonal (fun i => ((Real.exp (s i) : ℝ) : ℂ)) *
        (diagonal (φ w) * k w) := by
    intro w
    have hfun : (fun j => d w j * ((Real.exp (s j) : ℝ) : ℂ) * φ w j) =
        fun j => a w * ((r j : ℝ) : ℂ) := by
      funext j
      have he : ((Real.exp (-s j) : ℝ) : ℂ) * ((Real.exp (s j) : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, ← Real.exp_add]
        simp
      rw [hd]
      simp only
      rw [Complex.ofReal_mul]
      linear_combination (a w * (r j : ℂ) * ((Real.exp (-s j) : ℝ) : ℂ) * ((Real.exp (s j) : ℝ) : ℂ)) *
        hφn w j + a w * (r j : ℂ) * he
    conv_rhs => rw [← Matrix.mul_assoc, Matrix.mul_assoc (b w), Matrix.mul_assoc (b w),
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, hfun]
    have hsm : (diagonal fun j => a w * ((r j : ℝ) : ℂ)) = a w • diagonal (fun j => ((r j : ℝ) : ℂ)) := by
      ext i j
      simp [Matrix.diagonal_apply]
    rw [hsm, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨fun w => b w * diagonal (d w), fun w => diagonal (φ w) * k w, s, hs_sum, hs_step,
    fun w => (hb w).mul (Matrix.blockTriangular_diagonal _), ?_, ?_, ?_, hdetp,
    fun w => Submonoid.mul_mem _ (hdiagu w) (hk w), ?_, hmain⟩
  · intro w i j
    rw [hpn]
    calc ‖b w i j‖ * Real.exp (Real.log ‖a w‖ + Real.log (r j) - s j)
        ≤ M * Real.exp (3 * Real.log M) :=
          mul_le_mul (hbM w i j) (Real.exp_le_exp.mpr (he_up w j)) (Real.exp_pos _).le hM.le
      _ = Real.exp (4 * Real.log M) := by
          rw [show 4 * Real.log M = Real.log M + 3 * Real.log M by ring, Real.exp_add, Real.exp_log hM]
  · intro w i
    rw [hpdiag]
    exact Real.exp_le_exp.mpr (hd_low w i)
  · intro i
    simp only [hpdiag]
    rw [← Real.exp_sum, hprod0, Real.exp_zero]
  · intro w
    have h := congrArg Matrix.det (hmain w)
    rw [hdet w, Matrix.det_mul, Matrix.det_mul, hdetp, Matrix.det_diagonal, ← Complex.ofReal_prod,
      ← Real.exp_sum, hs_sum, Real.exp_zero, Complex.ofReal_one, one_mul, one_mul] at h
    exact h.symm

end PositivityTheory.KB.MomentRationality.Cz.Red
