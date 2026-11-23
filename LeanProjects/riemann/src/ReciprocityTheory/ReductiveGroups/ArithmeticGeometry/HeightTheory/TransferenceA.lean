import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.T0

open MeasureTheory Module Submodule

theorem gtA_countable {n : ℕ} (B : Basis (Fin n) ℝ (Fin n → ℝ)) :
    Countable (span ℤ (Set.range B)).toAddSubgroup := by
  have e : ((span ℤ (Set.range B) : Submodule ℤ (Fin n → ℝ)) : Set (Fin n → ℝ)) =
      Set.range (fun c : Fin n → ℤ => ∑ i, c i • B i) := by
    ext x
    simp only [SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun, Set.mem_range]
  have hc : ((span ℤ (Set.range B) : Submodule ℤ (Fin n → ℝ)) : Set (Fin n → ℝ)).Countable := by
    rw [e]
    exact Set.countable_range _
  exact hc.to_subtype

theorem gtA_mink_pi_lt {n : ℕ} (B : Basis (Fin n) ℝ (Fin n → ℝ)) {t : ℝ} (ht : 0 < t)
    (h : |(Matrix.of B).det| < t ^ n) :
    ∃ x ∈ span ℤ (Set.range B), x ≠ 0 ∧ ‖x‖ < t := by
  haveI := gtA_countable B
  have fund := ZSpan.isAddFundamentalDomain B volume
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (L := (span ℤ (Set.range B)).toAddSubgroup) fund (s := Metric.ball (0 : Fin n → ℝ) t) (fun y hy => by simpa using hy)
    (convex_ball (0 : Fin n → ℝ) t) (by
      have h2 : (2 : ENNReal) ^ n = ENNReal.ofReal ((2 : ℝ) ^ n) := by
        rw [ENNReal.ofReal_pow (by norm_num)]
        simp
      rw [ZSpan.volume_fundamentalDomain B, Real.volume_pi_ball 0 ht, Module.finrank_fin_fun,
        Fintype.card_fin, h2, ← ENNReal.ofReal_mul (abs_nonneg _),
        ENNReal.ofReal_lt_ofReal_iff (by positivity), mul_pow, mul_comm ((2 : ℝ) ^ n)]
      exact mul_lt_mul_of_pos_right h (by positivity))
  refine ⟨x, x.2, fun h0 => hx0 (Subtype.ext h0), ?_⟩
  simpa using hxs

theorem gtA_mink_pi_le {n : ℕ} (hn : 0 < n) (B : Basis (Fin n) ℝ (Fin n → ℝ)) {t : ℝ}
    (ht : 0 < t) (h : |(Matrix.of B).det| ≤ t ^ n) :
    ∃ x ∈ span ℤ (Set.range B), x ≠ 0 ∧ ‖x‖ ≤ t := by
  haveI := gtA_countable B
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have fund := ZSpan.isAddFundamentalDomain B volume
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (L := (span ℤ (Set.range B)).toAddSubgroup) fund (s := Metric.closedBall (0 : Fin n → ℝ) t) (fun y hy => by simpa using hy)
    (convex_closedBall (0 : Fin n → ℝ) t) (isCompact_closedBall (0 : Fin n → ℝ) t) (by
      have h2 : (2 : ENNReal) ^ n = ENNReal.ofReal ((2 : ℝ) ^ n) := by
        rw [ENNReal.ofReal_pow (by norm_num)]
        simp
      rw [ZSpan.volume_fundamentalDomain B, Real.volume_pi_closedBall 0 ht.le, Module.finrank_fin_fun,
        Fintype.card_fin, h2, ← ENNReal.ofReal_mul (abs_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      rw [mul_pow, mul_comm ((2 : ℝ) ^ n)]
      exact mul_le_mul_of_nonneg_right h (by positivity))
  refine ⟨x, x.2, fun h0 => hx0 (Subtype.ext h0), ?_⟩
  simpa using hxs

theorem gtA_norm_le_sqrt_mul (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ≤ Real.sqrt n * ‖EuclideanSpace.equiv (Fin n) ℝ x‖ := by
  rw [EuclideanSpace.norm_eq]
  have hM : ∀ i, ‖x i‖ ≤ ‖EuclideanSpace.equiv (Fin n) ℝ x‖ := fun i =>
    norm_le_pi_norm (EuclideanSpace.equiv (Fin n) ℝ x) i
  calc Real.sqrt (∑ i, ‖x i‖ ^ 2)
      ≤ Real.sqrt (∑ _i : Fin n, ‖EuclideanSpace.equiv (Fin n) ℝ x‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        exact Finset.sum_le_sum fun i _ => by gcongr; exact hM i
    _ = Real.sqrt n * ‖EuclideanSpace.equiv (Fin n) ℝ x‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem gtB_inner_eq (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x y = ∑ k, EuclideanSpace.equiv (Fin n) ℝ x k * EuclideanSpace.equiv (Fin n) ℝ y k := by
  first
    | simp [PiLp.inner_apply, mul_comm]
    | (rw [EuclideanSpace.inner_eq_star_dotProduct]; simp [dotProduct, mul_comm])

theorem gtB_nondeg (n : ℕ) : (innerₗ (EuclideanSpace ℝ (Fin n))).Nondegenerate := by
  show _ ∧ _
  constructor
  · intro x hx
    first
      | simpa using hx x
      | simpa [innerₗ_apply_apply] using hx x
  · intro y hy
    first
      | simpa using hy y
      | simpa [innerₗ_apply_apply] using hy y

theorem gtB_dual_short {n : ℕ} (hn : 0 < n) (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ x ∈ span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖) :
    ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧ (∀ j, ∃ m : ℤ, inner ℝ y (b j) = m) ∧
      ‖y‖ ≤ n / lam := by
  set e := EuclideanSpace.equiv (Fin n) ℝ with he
  set B := b.map e.toLinearEquiv with hBdef
  have hB : ∀ j, B j = e (b j) := fun j => by simp [B]
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hdet : (lam / Real.sqrt n) ^ n ≤ |(Matrix.of B).det| := by
    by_contra hlt
    push Not at hlt
    obtain ⟨x, hxs, hx0, hxn⟩ := gtA_mink_pi_lt B (by positivity) hlt
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hxs
    have hex : e (∑ i, c i • b i) = ∑ i, c i • B i := by simp [hB, map_sum, map_zsmul]
    have hx'0 : (∑ i, c i • b i) ≠ 0 := by intro h; apply hx0; rw [← hex, h, map_zero]
    have h1 := hmin _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) hx'0
    have h2 := gtA_norm_le_sqrt_mul n (∑ i, c i • b i)
    rw [hex] at h2
    have : Real.sqrt n * ‖∑ i, c i • B i‖ < lam := by
      calc _ < Real.sqrt n * (lam / Real.sqrt n) := mul_lt_mul_of_pos_left hxn hsq
        _ = lam := by field_simp
    linarith
  set c := LinearMap.BilinForm.dualBasis (innerₗ (EuclideanSpace ℝ (Fin n))) (gtB_nondeg n) b with hcdef
  have hc : ∀ i j, inner ℝ (c i) (b j) = if j = i then 1 else 0 := fun i j => by
    have := LinearMap.BilinForm.apply_dualBasis_left (gtB_nondeg n) b i j
    simpa using this
  set C := c.map e.toLinearEquiv with hCdef
  have hC : ∀ j, C j = e (c j) := fun j => by simp [C]
  have hCB : Matrix.of C * (Matrix.of B).transpose = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.one_apply, hB, hC]
    rw [← gtB_inner_eq, hc]
    simp [eq_comm]
  have hdetCB : (Matrix.of C).det * (Matrix.of B).det = 1 := by
    rw [← Matrix.det_transpose (Matrix.of B), ← Matrix.det_mul, hCB, Matrix.det_one]
  have hdetC : |(Matrix.of C).det| ≤ (Real.sqrt n / lam) ^ n := by
    have hpos : 0 < (lam / Real.sqrt n) ^ n := by positivity
    have h1 : |(Matrix.of C).det| * |(Matrix.of B).det| = 1 := by rw [← abs_mul, hdetCB, abs_one]
    have h2 : |(Matrix.of C).det| = |(Matrix.of B).det|⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2, show (Real.sqrt n / lam) ^ n = ((lam / Real.sqrt n) ^ n)⁻¹ by
      rw [← inv_pow, inv_div]]
    exact inv_anti₀ hpos hdet
  obtain ⟨x, hxs, hx0, hxn⟩ := gtA_mink_pi_le hn C (by positivity) hdetC
  obtain ⟨k, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hxs
  have hex : e (∑ i, k i • c i) = ∑ i, k i • C i := by simp [hC, map_sum, map_zsmul]
  refine ⟨∑ i, k i • c i, ?_, ?_, ?_⟩
  · intro h; apply hx0; rw [← hex, h, map_zero]
  · intro j
    refine ⟨k j, ?_⟩
    rw [sum_inner]
    simp_rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hc]
    simp
  · have h2 := gtA_norm_le_sqrt_mul n (∑ i, k i • c i)
    rw [hex] at h2
    calc _ ≤ _ := h2
      _ ≤ Real.sqrt n * (Real.sqrt n / lam) := mul_le_mul_of_nonneg_left hxn hsq.le
      _ = n / lam := by
        rw [← mul_div_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _)]

end ReciprocityTheory.ChartRestriction.G.T0
