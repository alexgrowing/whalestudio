import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.HfNegRight

namespace ReciprocityTheory.ChartRestriction.G.I2.FPw

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

open Classical

theorem detM_eq (Y : GT ι) (b₀ : OrthonormalBasis (Fin (2 * Fintype.card ι)) ℝ (EuclideanSpace ℂ ι)) :
    |b₀.toBasis.det Y.b| = 1 := by
  have hM : ∀ i k, ∃ m : ℤ, (Hf (Y.b i) (Y.b k)).im = m := fun i k =>
    Y.integral _ _ (Submodule.subset_span ⟨i, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
  choose m hm using hM
  have hG : lemSG Y.b = (Matrix.of m).map (Int.cast : ℤ → ℝ) := by
    ext i k; simp [lemSG, hm]
  obtain ⟨C, hC⟩ := lemSG_inv Y
  have h1 := congrArg Matrix.det hC
  rw [Matrix.det_mul, Matrix.det_one] at h1
  have h2 := h1
  rw [hG, ← Int.cast_det, ← Int.cast_det] at h2
  have h3 : C.det * (Matrix.of m).det = 1 := by exact_mod_cast h2
  have h4 : |(Matrix.of m).det| = 1 := by
    have h3' : (Matrix.of m).det * C.det = 1 := by rw [mul_comm]; exact h3
    rcases Int.eq_one_or_neg_one_of_mul_eq_one h3' with h | h <;> rw [h] <;> rfl
  have h5 : |(lemSG Y.b).det| = 1 := by
    rw [hG, ← Int.cast_det, ← Int.cast_abs, h4, Int.cast_one]
  rw [lemSG_det Y.b b₀, abs_mul, abs_mul, lemSJ_det, one_mul] at h5
  have hd := abs_nonneg (b₀.toBasis.det Y.b)
  nlinarith

theorem vol_eq (Y : GT ι) : volume (ZSpan.fundamentalDomain Y.b) = 1 := by
  have hfr : Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * Fintype.card ι := by
    first
      | (rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι), Complex.finrank_real_complex,
          finrank_euclideanSpace])
      | simp [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι)]
  let b₀ : OrthonormalBasis (Fin (2 * Fintype.card ι)) ℝ (EuclideanSpace ℂ ι) :=
    (stdOrthonormalBasis ℝ (EuclideanSpace ℂ ι)).reindex (finCongr hfr)
  rw [ZSpan.measure_fundamentalDomain Y.b volume b₀.toBasis, detM_eq Y b₀,
    measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped b₀.toBasis volume),
    OrthonormalBasis.coe_toBasis, b₀.volume_parallelepiped]
  simp

theorem paU_pt {q c : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a v : EuclideanSpace ℂ ι, ‖paU q a F v‖ ≤
      C * (1 + ‖v‖) ^ c * Real.exp ((q * Real.pi) * ‖v‖ ^ 2) *
        ((1 + ‖a‖) ^ (2 * c) * Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 4)) := by
  obtain ⟨C1, hC1, h1⟩ := paPoly_growth hF
  refine ⟨C1, hC1, fun a v => ?_⟩
  have hn := paU_norm_mul q a v F
  have hW : paW q v * Real.exp ((q * Real.pi) * ‖v‖ ^ 2) = 1 := by
    rw [paW, ← Real.exp_add]; simp
  have hE1 : Real.exp (-(q * Real.pi) * ‖v - (1 / 2 : ℂ) • a‖ ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (q : ℝ) * Real.pi := by positivity
    nlinarith [sq_nonneg ‖v - (1 / 2 : ℂ) • a‖]
  have hva : 1 + ‖v - a‖ ≤ (1 + ‖v‖) * (1 + ‖a‖) := by
    nlinarith [norm_sub_le v a, norm_nonneg v, norm_nonneg a, mul_nonneg (norm_nonneg v) (norm_nonneg a)]
  have ha : (1 + ‖a‖) ^ c ≤ (1 + ‖a‖) ^ (2 * c) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg a]) (by omega)
  have E2 := Real.exp_pos (-(q * Real.pi) * ‖a‖ ^ 2 / 4)
  have EV := Real.exp_pos ((q * Real.pi) * ‖v‖ ^ 2)
  have hU : ‖paU q a F v‖ = (‖paU q a F v‖ * paW q v) * Real.exp ((q * Real.pi) * ‖v‖ ^ 2) := by
    rw [mul_assoc, hW, mul_one]
  rw [hU, hn]
  have k1 : ‖F (v - a)‖ ≤ C1 * ((1 + ‖v‖) ^ c * (1 + ‖a‖) ^ (2 * c)) := by
    refine (h1 _).trans (mul_le_mul_of_nonneg_left ?_ hC1)
    calc (1 + ‖v - a‖) ^ c ≤ ((1 + ‖v‖) * (1 + ‖a‖)) ^ c :=
          pow_le_pow_left₀ (by linarith [norm_nonneg (v - a)]) hva c
      _ = (1 + ‖v‖) ^ c * (1 + ‖a‖) ^ c := mul_pow _ _ _
      _ ≤ (1 + ‖v‖) ^ c * (1 + ‖a‖) ^ (2 * c) :=
          mul_le_mul_of_nonneg_left ha (by positivity)
  have hFn := norm_nonneg (F (v - a))
  have hE1p := Real.exp_pos (-(q * Real.pi) * ‖v - (1 / 2 : ℂ) • a‖ ^ 2)
  calc ‖F (v - a)‖ * (Real.exp (-(q * Real.pi) * ‖v - (1 / 2 : ℂ) • a‖ ^ 2) *
        Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 4)) * Real.exp ((q * Real.pi) * ‖v‖ ^ 2)
      ≤ ‖F (v - a)‖ * (1 * Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 4)) *
          Real.exp ((q * Real.pi) * ‖v‖ ^ 2) := by gcongr
    _ ≤ C1 * ((1 + ‖v‖) ^ c * (1 + ‖a‖) ^ (2 * c)) * (1 * Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 4)) *
          Real.exp ((q * Real.pi) * ‖v‖ ^ 2) := by gcongr
    _ = _ := by ring

end

end ReciprocityTheory.ChartRestriction.G.I2.FPw
