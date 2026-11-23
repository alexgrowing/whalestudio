import Mathlib

noncomputable section

namespace ReciprocityTheory.ReducedBases.T2

open Finset InnerProductSpace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}

abbrev gs (b : Fin d → E) : Fin d → E := gramSchmidt ℝ b

def mu (b : Fin d → E) (i j : Fin d) : ℝ := ⟪gs b j, b i⟫_ℝ / ‖gs b j‖ ^ 2

def nu (b : Fin d → E) (c : Fin d → ℝ) (j : Fin d) : ℝ := ∑ l, c l * mu b l j

lemma gs_inner_b_of_lt (b : Fin d → E) {i j : Fin d} (h : i < j) : ⟪gs b j, b i⟫_ℝ = 0 :=
  gramSchmidt_inv_triangular ℝ b h

lemma gs_orth (b : Fin d → E) {i j : Fin d} (h : i ≠ j) : ⟪gs b i, gs b j⟫_ℝ = 0 :=
  gramSchmidt_orthogonal ℝ b h

lemma b_sub_gs_mem (b : Fin d → E) (k : Fin d) : b k - gs b k ∈ span ℝ (b '' Set.Iio k) := by
  rw [← span_gramSchmidt_Iio ℝ b k]
  have hdef := gramSchmidt_def ℝ b k
  have hrw : b k - gs b k = b k - gramSchmidt ℝ b k := rfl
  rw [hrw, hdef, sub_sub_cancel]
  refine Submodule.sum_mem _ fun i hi => ?_
  have hsub : (ℝ ∙ gramSchmidt ℝ b i) ≤ span ℝ (gramSchmidt ℝ b '' Set.Iio k) := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact subset_span ⟨i, Finset.mem_Iio.mp hi, rfl⟩
  apply hsub
  first
    | exact Submodule.coe_mem _
    | exact Submodule.starProjection_apply_mem _ _
    | simp

lemma inner_gs_span (b : Fin d → E) (k : Fin d) {y : E} (hy : y ∈ span ℝ (b '' Set.Iio k)) :
    ⟪gs b k, y⟫_ℝ = 0 := by
  have hle : span ℝ (gramSchmidt ℝ b '' Set.Iio k) ≤ (ℝ ∙ gs b k)ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact gramSchmidt_orthogonal ℝ b (ne_of_gt hi)
  rw [← span_gramSchmidt_Iio ℝ b k] at hy
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hy)

lemma gs_eq_of (b : Fin d → E) (k : Fin d) (v : E) (h1 : b k - v ∈ span ℝ (b '' Set.Iio k))
    (h2 : ∀ j < k, ⟪v, b j⟫_ℝ = 0) : gs b k = v := by
  have hle : span ℝ (b '' Set.Iio k) ≤ (ℝ ∙ v)ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact h2 j hj
  have hmem : gs b k - v ∈ span ℝ (b '' Set.Iio k) := by
    have h3 := Submodule.sub_mem _ h1 (b_sub_gs_mem b k)
    have h4 : b k - v - (b k - gs b k) = gs b k - v := by abel
    rwa [h4] at h3
  have h0 : ⟪gs b k - v, gs b k - v⟫_ℝ = 0 := by
    rw [inner_sub_left, inner_gs_span b k hmem,
      Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hmem), sub_zero]
  rw [← sub_eq_zero]
  exact inner_self_eq_zero.1 h0

lemma inner_gs_b_self (b : Fin d → E) (k : Fin d) : ⟪gs b k, b k⟫_ℝ = ‖gs b k‖ ^ 2 := by
  have h0 := inner_gs_span b k (b_sub_gs_mem b k)
  rw [inner_sub_right, sub_eq_zero] at h0
  rw [h0, real_inner_self_eq_norm_sq]

lemma gs_ne_zero (b : Fin d → E) (hb : LinearIndependent ℝ b) (k : Fin d) : gs b k ≠ 0 :=
  gramSchmidt_ne_zero k hb

lemma mu_self (b : Fin d → E) (hb : LinearIndependent ℝ b) (k : Fin d) : mu b k k = 1 := by
  unfold mu
  rw [inner_gs_b_self, div_self]
  exact pow_ne_zero _ (norm_ne_zero_iff.mpr (gs_ne_zero b hb k))

lemma mu_of_lt (b : Fin d → E) {i j : Fin d} (h : i < j) : mu b i j = 0 := by
  unfold mu
  rw [gs_inner_b_of_lt b h, zero_div]

private lemma inner_gs_sum_smul_gs (b : Fin d → E) (x : Fin d → ℝ) (j : Fin d) :
    ⟪gs b j, ∑ k, x k • gs b k⟫_ℝ = x j * ‖gs b j‖ ^ 2 := by
  rw [inner_sum, Finset.sum_eq_single j]
  · rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  · intro k _ hk
    rw [real_inner_smul_right, gs_orth b (Ne.symm hk), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

private lemma eq_zero_of_mem_span_gs_of_inner_eq_zero (b : Fin d → E) {y : E} (hy : y ∈ span ℝ (Set.range (gs b)))
    (h : ∀ j, ⟪gs b j, y⟫_ℝ = 0) : y = 0 := by
  have hle : span ℝ (Set.range (gs b)) ≤ (ℝ ∙ y)ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
    exact h j
  exact inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hy))

private lemma mu_mul_norm_gs_sq (b : Fin d → E) (hb : LinearIndependent ℝ b) (i j : Fin d) :
    mu b i j * ‖gs b j‖ ^ 2 = ⟪gs b j, b i⟫_ℝ := by
  have hne : ‖gs b j‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (gs_ne_zero b hb j))
  unfold mu
  first
    | exact div_mul_cancel₀ _ hne
    | field_simp

lemma b_eq_sum (b : Fin d → E) (hb : LinearIndependent ℝ b) (i : Fin d) :
    b i = ∑ j, mu b i j • gs b j := by
  rw [← sub_eq_zero]
  apply eq_zero_of_mem_span_gs_of_inner_eq_zero b
  · refine Submodule.sub_mem _ ?_ ?_
    · exact span_mono (Set.image_subset_range _ _) (mem_span_gramSchmidt ℝ b le_rfl)
    · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (subset_span ⟨j, rfl⟩)
  · intro j
    rw [inner_sub_right, inner_gs_sum_smul_gs, mu_mul_norm_gs_sq b hb, sub_self]

lemma sum_smul_b (b : Fin d → E) (hb : LinearIndependent ℝ b) (c : Fin d → ℝ) :
    ∑ l, c l • b l = ∑ j, nu b c j • gs b j := by
  calc ∑ l, c l • b l = ∑ l, ∑ j, (c l * mu b l j) • gs b j := by
        refine Finset.sum_congr rfl fun l _ => ?_
        conv_lhs => rw [b_eq_sum b hb l]
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => smul_smul _ _ _
    _ = ∑ j, nu b c j • gs b j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [nu, Finset.sum_smul]

lemma inner_gs_sum (b : Fin d → E) (x : Fin d → ℝ) (j : Fin d) :
    ⟪gs b j, ∑ k, x k • gs b k⟫_ℝ = x j * ‖gs b j‖ ^ 2 := by
  exact inner_gs_sum_smul_gs b x j

lemma inner_gs_comb (b : Fin d → E) (hb : LinearIndependent ℝ b) (c : Fin d → ℝ) (j : Fin d) :
    ⟪gs b j, ∑ l, c l • b l⟫_ℝ = nu b c j * ‖gs b j‖ ^ 2 := by
  rw [sum_smul_b b hb c, inner_gs_sum]

lemma norm_sq_comb (b : Fin d → E) (hb : LinearIndependent ℝ b) (c : Fin d → ℝ) :
    ‖∑ l, c l • b l‖ ^ 2 = ∑ j, nu b c j ^ 2 * ‖gs b j‖ ^ 2 := by
  rw [sum_smul_b b hb c, ← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_left, inner_gs_sum]
  ring

end ReciprocityTheory.ReducedBases.T2

end
