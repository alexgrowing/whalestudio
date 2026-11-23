import Mathlib

namespace ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall

open MeasureTheory

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sqBall (r : ℕ) (E : Type*) [NormedAddCommGroup E] (R : ℝ) : Set (Fin r → E) :=
  {u | ∑ k, ‖u k‖ ^ 2 ≤ R ^ 2}

lemma norm_sq_convex_comb {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (z w : E) :
    ‖a • z + b • w‖ ^ 2 ≤ a * ‖z‖ ^ 2 + b * ‖w‖ ^ 2 := by
  have h1 : ‖a • z + b • w‖ ≤ a * ‖z‖ + b * ‖w‖ := by
    calc ‖a • z + b • w‖ ≤ ‖a • z‖ + ‖b • w‖ := norm_add_le _ _
      _ = a * ‖z‖ + b * ‖w‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  have h2 : (a * ‖z‖ + b * ‖w‖) ^ 2 ≤ a * ‖z‖ ^ 2 + b * ‖w‖ ^ 2 := by
    obtain rfl : b = 1 - a := by linarith
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (‖z‖ - ‖w‖))]
  calc ‖a • z + b • w‖ ^ 2 ≤ (a * ‖z‖ + b * ‖w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

lemma sqBall_convex (r : ℕ) (R : ℝ) : Convex ℝ (sqBall r E R) := by
  intro u hu v hv a b ha hb hab
  simp only [sqBall, Set.mem_setOf_eq] at hu hv ⊢
  calc ∑ k, ‖(a • u + b • v) k‖ ^ 2 = ∑ k, ‖a • u k + b • v k‖ ^ 2 := rfl
    _ ≤ ∑ k, (a * ‖u k‖ ^ 2 + b * ‖v k‖ ^ 2) :=
        Finset.sum_le_sum fun k _ => norm_sq_convex_comb ha hb hab _ _
    _ = a * ∑ k, ‖u k‖ ^ 2 + b * ∑ k, ‖v k‖ ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ a * R ^ 2 + b * R ^ 2 := by gcongr
    _ = R ^ 2 := by rw [← add_mul, hab, one_mul]

lemma sqBall_neg (r : ℕ) (R : ℝ) : ∀ u ∈ sqBall r E R, -u ∈ sqBall r E R := by
  intro u hu
  simpa [sqBall] using hu

lemma sqBall_subset (r : ℕ) (R : ℝ) : sqBall r E R ⊆ Metric.closedBall 0 |R| := by
  intro u hu
  simp only [sqBall, Set.mem_setOf_eq] at hu
  rw [mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg (abs_nonneg R)).2 fun k => ?_
  have hk : ‖u k‖ ^ 2 ≤ R ^ 2 :=
    (Finset.single_le_sum (f := fun k => ‖u k‖ ^ 2) (fun k _ => by positivity)
      (Finset.mem_univ k)).trans hu
  have := sq_le_sq.mp hk
  rwa [abs_of_nonneg (norm_nonneg _)] at this

lemma sqBall_isBounded (r : ℕ) (R : ℝ) : Bornology.IsBounded (sqBall r E R) := Metric.isBounded_closedBall.subset (sqBall_subset r R)

lemma sqBall_isClosed (r : ℕ) (R : ℝ) : IsClosed (sqBall r E R) := by
  unfold sqBall
  exact isClosed_le (continuous_finset_sum _ fun k _ => (continuous_apply k).norm.pow 2)
    continuous_const

lemma box_subset_sqBall (r : ℕ) {R : ℝ} :
    Set.pi Set.univ (fun _ : Fin r => Metric.closedBall (0 : E) (R / Real.sqrt r)) ⊆
      sqBall r E R := by
  intro u hu
  rw [Set.mem_univ_pi] at hu
  simp only [sqBall, Set.mem_setOf_eq]
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
    positivity
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hb : ∀ k, ‖u k‖ ^ 2 ≤ R ^ 2 / r := by
    intro k
    have h := mem_closedBall_zero_iff.mp (hu k)
    calc ‖u k‖ ^ 2 ≤ (R / Real.sqrt r) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = R ^ 2 / r := by rw [div_pow, Real.sq_sqrt hr'.le]
  calc ∑ k, ‖u k‖ ^ 2 ≤ ∑ _k : Fin r, R ^ 2 / r := Finset.sum_le_sum fun k _ => hb k
    _ = R ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace V] [BorelSpace V]

end Generic

end ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall
