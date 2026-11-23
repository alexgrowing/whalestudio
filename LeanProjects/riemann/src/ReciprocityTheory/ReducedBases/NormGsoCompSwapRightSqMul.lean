import ReciprocityTheory.ReducedBases.LatticeReduction

noncomputable section

namespace ReciprocityTheory.ReducedBases.T2

open Finset InnerProductSpace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}

def pot (b : Fin d → E) : ℝ :=
  ∏ k, ∏ j ∈ univ.filter (fun j : Fin d => j ≤ k), ‖gs b j‖ ^ 2

lemma swap_lt (j j1 : Fin d) (hj : j1.val = j.val + 1) (k : Fin d) (hk : k ≠ j1) (l : Fin d)
    (hl : l < k) : Equiv.swap j j1 l < k := by
  by_cases h1 : l = j
  · rw [h1, Equiv.swap_apply_left]
    rw [h1] at hl
    have : k.val ≠ j1.val := fun h => hk (Fin.ext h)
    rw [Fin.lt_iff_val_lt_val] at hl ⊢
    omega
  · by_cases h2 : l = j1
    · rw [h2, Equiv.swap_apply_right]
      rw [h2] at hl
      rw [Fin.lt_iff_val_lt_val] at hl ⊢
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      exact hl

lemma swap_img (b : Fin d → E) (j j1 : Fin d) (hj : j1.val = j.val + 1) (k : Fin d)
    (hk : k ≠ j1) : (b ∘ Equiv.swap j j1) '' Set.Iio k = b '' Set.Iio k := by
  have hs : (Equiv.swap j j1) '' Set.Iio k = Set.Iio k := by
    ext l
    simp only [Set.mem_image, Set.mem_Iio]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact swap_lt j j1 hj k hk m hm
    · intro hl
      exact ⟨Equiv.swap j j1 l, swap_lt j j1 hj k hk l hl, Equiv.swap_apply_self _ _ _⟩
  rw [Set.image_comp, hs]

lemma swap_gs_other (b : Fin d → E) (j j1 : Fin d) (hj : j1.val = j.val + 1) (k : Fin d)
    (hk : k ≠ j) (hk1 : k ≠ j1) : gs (b ∘ Equiv.swap j j1) k = gs b k := by
  have hkk : Equiv.swap j j1 k = k := Equiv.swap_apply_of_ne_of_ne hk hk1
  refine gs_eq_of _ _ _ ?_ ?_
  · rw [swap_img b j j1 hj k hk1]
    simp only [Function.comp_apply, hkk]
    exact b_sub_gs_mem b k
  · intro i hi
    apply inner_gs_span b k
    apply Submodule.subset_span
    exact ⟨Equiv.swap j j1 i, swap_lt j j1 hj k hk1 i hi, rfl⟩

lemma swap_gs_j (b : Fin d → E) (hb : LinearIndependent ℝ b) (j j1 : Fin d)
    (hj : j1.val = j.val + 1) :
    gs (b ∘ Equiv.swap j j1) j = gs b j1 + mu b j1 j • gs b j := by
  have hne : j ≠ j1 := fun h => by rw [Fin.ext_iff] at h; omega
  have hne' : j1 ≠ j := fun h => hne h.symm
  have hsj : Equiv.swap j j1 j = j1 := Equiv.swap_apply_left j j1
  have hI : Set.Iio j1 = insert j (Set.Iio j) := by
    ext l
    simp only [Set.mem_Iio, Set.mem_insert_iff, Fin.lt_iff_val_lt_val, Fin.ext_iff]
    omega
  have hmem := b_sub_gs_mem b j1
  rw [hI, Set.image_insert_eq, Submodule.mem_span_insert] at hmem
  obtain ⟨c, s, hs, hcs⟩ := hmem
  have hG0 : ‖gs b j‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (gs_ne_zero b hb j))
  have hc : c = mu b j1 j := by
    have h1 : ⟪gs b j, b j1 - gs b j1⟫_ℝ = mu b j1 j * ‖gs b j‖ ^ 2 := by
      rw [inner_sub_right, gs_orth b hne, sub_zero]
      unfold mu
      rw [div_mul_cancel₀ _ hG0]
    have h2 : ⟪gs b j, b j1 - gs b j1⟫_ℝ = c * ‖gs b j‖ ^ 2 := by
      rw [hcs, inner_add_right, real_inner_smul_right, inner_gs_b_self, inner_gs_span b j hs, add_zero]
    exact mul_right_cancel₀ hG0 (h2.symm.trans h1)
  subst hc
  refine gs_eq_of _ _ _ ?_ ?_
  · rw [swap_img b j j1 hj j hne]
    simp only [Function.comp_apply, hsj]
    have he : b j1 - (gs b j1 + mu b j1 j • gs b j) = mu b j1 j • (b j - gs b j) + s := by
      rw [sub_add_eq_sub_sub, hcs, smul_sub]
      abel
    rw [he]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (b_sub_gs_mem b j)) hs
  · intro i hi
    have hi1 : i < j1 := lt_trans hi (by rw [Fin.lt_iff_val_lt_val]; omega)
    have hsi : Equiv.swap j j1 i = i := Equiv.swap_apply_of_ne_of_ne (ne_of_lt hi) (ne_of_lt hi1)
    simp only [Function.comp_apply, hsi]
    rw [inner_add_left, real_inner_smul_left, gs_inner_b_of_lt b hi1, gs_inner_b_of_lt b hi]
    ring

lemma norm_swap_j (b : Fin d → E) (j j1 : Fin d) (hj : j1.val = j.val + 1) :
    ‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 = ‖gs b j1‖ ^ 2 + mu b j1 j ^ 2 * ‖gs b j‖ ^ 2 := by
  have hne : j1 ≠ j := fun h => by rw [Fin.ext_iff] at h; omega
  rw [norm_add_sq_real, real_inner_smul_right, gs_orth b hne, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs]
  ring

lemma norm_gso_comp_swap_right_sq_mul (b : Fin d → E) (hb : LinearIndependent ℝ b) (j j1 : Fin d)
    (hj : j1.val = j.val + 1) :
    ‖gs (b ∘ Equiv.swap j j1) j1‖ ^ 2 * ‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 =
      ‖gs b j‖ ^ 2 * ‖gs b j1‖ ^ 2 := by
  have hne : j ≠ j1 := fun h => by rw [Fin.ext_iff] at h; omega
  have hjlt : j < j1 := by rw [Fin.lt_iff_val_lt_val]; omega
  have hb' : LinearIndependent ℝ (b ∘ Equiv.swap j j1) := hb.comp _ (Equiv.injective _)
  have hu := swap_gs_j b hb j j1 hj
  have hN := norm_swap_j b j j1 hj
  have hN0 : ‖gs (b ∘ Equiv.swap j j1) j‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (gs_ne_zero _ hb' j))
  have hG0 : ‖gs b j‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (gs_ne_zero b hb j))
  have hv : gs (b ∘ Equiv.swap j j1) j1 = gs b j -
      (mu b j1 j * ‖gs b j‖ ^ 2 / ‖gs (b ∘ Equiv.swap j j1) j‖ ^ 2) • gs (b ∘ Equiv.swap j j1) j := by
    refine gs_eq_of _ _ _ ?_ ?_
    · have hmono : span ℝ ((b ∘ Equiv.swap j j1) '' Set.Iio j) ≤
          span ℝ ((b ∘ Equiv.swap j j1) '' Set.Iio j1) :=
        Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (le_of_lt hjlt)))
      have hbj : (b ∘ Equiv.swap j j1) j ∈ span ℝ ((b ∘ Equiv.swap j j1) '' Set.Iio j1) :=
        Submodule.subset_span ⟨j, hjlt, rfl⟩
      have hgs : gs (b ∘ Equiv.swap j j1) j ∈ span ℝ ((b ∘ Equiv.swap j j1) '' Set.Iio j1) := by
        have h := Submodule.sub_mem _ hbj (hmono (b_sub_gs_mem (b ∘ Equiv.swap j j1) j))
        rwa [sub_sub_cancel] at h
      have hB : b j - gs b j ∈ span ℝ ((b ∘ Equiv.swap j j1) '' Set.Iio j1) := by
        apply hmono
        rw [swap_img b j j1 hj j hne]
        exact b_sub_gs_mem b j
      have hbj1 : (b ∘ Equiv.swap j j1) j1 = b j := by simp [Equiv.swap_apply_right]
      rw [hbj1]
      have he : ∀ (t : ℝ) (x : E), b j - (gs b j - t • x) = (b j - gs b j) + t • x := by
        intro t x; abel
      rw [he]
      exact Submodule.add_mem _ hB (Submodule.smul_mem _ _ hgs)
    · intro i hi
      have hij : i ≤ j := by
        rw [Fin.le_iff_val_le_val]; rw [Fin.lt_iff_val_lt_val] at hi; omega
      rcases lt_or_eq_of_le hij with h | h
      · have hsi : Equiv.swap j j1 i = i :=
          Equiv.swap_apply_of_ne_of_ne (ne_of_lt h) (ne_of_lt (lt_trans h hjlt))
        rw [inner_sub_left, real_inner_smul_left, gs_inner_b_of_lt _ h]
        simp only [Function.comp_apply, hsi, gs_inner_b_of_lt b h]
        ring
      · rw [h, inner_sub_left, real_inner_smul_left, inner_gs_b_self (b ∘ Equiv.swap j j1) j]
        have hsj : (b ∘ Equiv.swap j j1) j = b j1 := by simp
        have hmu : ⟪gs b j, b j1⟫_ℝ = mu b j1 j * ‖gs b j‖ ^ 2 := by
          unfold mu
          rw [div_mul_cancel₀ _ hG0]
        rw [hsj, hmu, div_mul_cancel₀ _ hN0, sub_self]
  have hip : ⟪gs b j, gs (b ∘ Equiv.swap j j1) j⟫_ℝ = mu b j1 j * ‖gs b j‖ ^ 2 := by
    rw [hu, inner_add_right, real_inner_smul_right, gs_orth b hne, real_inner_self_eq_norm_sq]
    ring
  have hN' : ‖gs (b ∘ Equiv.swap j j1) j‖ ^ 2 = ‖gs b j1‖ ^ 2 + mu b j1 j ^ 2 * ‖gs b j‖ ^ 2 := by
    rw [hu, hN]
  rw [hv, ← hu, norm_sub_sq_real, real_inner_smul_right, hip, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, hN']
  have hD : ‖gs b j1‖ ^ 2 + mu b j1 j ^ 2 * ‖gs b j‖ ^ 2 ≠ 0 := hN' ▸ hN0
  have key : mu b j1 j * ‖gs b j‖ ^ 2 / (‖gs b j1‖ ^ 2 + mu b j1 j ^ 2 * ‖gs b j‖ ^ 2) *
      (‖gs b j1‖ ^ 2 + mu b j1 j ^ 2 * ‖gs b j‖ ^ 2) = mu b j1 j * ‖gs b j‖ ^ 2 :=
    div_mul_cancel₀ _ hD
  linear_combination (mu b j1 j * ‖gs b j‖ ^ 2 / (‖gs b j1‖ ^ 2 + mu b j1 j ^ 2 * ‖gs b j‖ ^ 2) *
      (‖gs b j1‖ ^ 2 + mu b j1 j ^ 2 * ‖gs b j‖ ^ 2) - mu b j1 j * ‖gs b j‖ ^ 2) * key

private lemma prod_filter_le_ite_eq_of_mul_eq_one (j j1 : Fin d) (hj : j1.val = j.val + 1) (A B : ℝ) (hAB : A * B = 1)
    (k : Fin d) :
    ∏ i ∈ univ.filter (fun i : Fin d => i ≤ k),
        ((if i = j then A else 1) * (if i = j1 then B else 1)) = if k = j then A else 1 := by
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
  rcases lt_trichotomy k j with h | h | h
  · have h1 : ¬ j ≤ k := not_le.mpr h
    have h2 : ¬ j1 ≤ k := by
      rw [Fin.le_iff_val_le_val]; rw [Fin.lt_iff_val_lt_val] at h; omega
    rw [if_neg h1, if_neg h2, if_neg (ne_of_lt h), one_mul]
  · have h2 : ¬ j1 ≤ j := by rw [Fin.le_iff_val_le_val]; omega
    rw [h, if_pos le_rfl, if_neg h2, if_pos rfl, mul_one]
  · have h1 : j ≤ k := le_of_lt h
    have h2 : j1 ≤ k := by
      rw [Fin.le_iff_val_le_val]; rw [Fin.lt_iff_val_lt_val] at h; omega
    rw [if_pos h1, if_pos h2, if_neg (ne_of_gt h), hAB]

lemma pot_swap (b : Fin d → E) (hb : LinearIndependent ℝ b) (j j1 : Fin d)
    (hj : j1.val = j.val + 1) :
    pot (b ∘ Equiv.swap j j1) =
      pot b * (‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 / ‖gs b j‖ ^ 2) := by
  have hne : j ≠ j1 := fun h => by rw [Fin.ext_iff] at h; omega
  have hb' : LinearIndependent ℝ (b ∘ Equiv.swap j j1) := hb.comp _ (Equiv.injective _)
  have hG0 : ‖gs b j‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (gs_ne_zero b hb j))
  have hU0 : ‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 ≠ 0 := by
    rw [← swap_gs_j b hb j j1 hj]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (gs_ne_zero _ hb' j))
  have hf : ∀ i, ‖gs (b ∘ Equiv.swap j j1) i‖ ^ 2 =
      ‖gs b i‖ ^ 2 * ((if i = j then ‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 / ‖gs b j‖ ^ 2 else 1) *
        (if i = j1 then ‖gs b j‖ ^ 2 / ‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 else 1)) := by
    intro i
    by_cases h1 : i = j
    · rw [h1, if_pos rfl, if_neg hne, swap_gs_j b hb j j1 hj, mul_one, mul_comm,
        div_mul_cancel₀ _ hG0]
    · by_cases h2 : i = j1
      · rw [h2, if_neg (Ne.symm hne), if_pos rfl, one_mul, mul_div_assoc', eq_div_iff hU0]
        linear_combination norm_gso_comp_swap_right_sq_mul b hb j j1 hj
      · rw [if_neg h1, if_neg h2, swap_gs_other b j j1 hj i h1 h2]
        ring
  have hAB : ‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 / ‖gs b j‖ ^ 2 *
      (‖gs b j‖ ^ 2 / ‖gs b j1 + mu b j1 j • gs b j‖ ^ 2) = 1 := by
    rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hG0 hU0)]
    ring
  have hk : ∀ k : Fin d, ∏ i ∈ univ.filter (fun i : Fin d => i ≤ k),
      ‖gs (b ∘ Equiv.swap j j1) i‖ ^ 2 =
      (∏ i ∈ univ.filter (fun i : Fin d => i ≤ k), ‖gs b i‖ ^ 2) *
        (if k = j then ‖gs b j1 + mu b j1 j • gs b j‖ ^ 2 / ‖gs b j‖ ^ 2 else 1) := by
    intro k
    rw [← prod_filter_le_ite_eq_of_mul_eq_one j j1 hj _ _ hAB k, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => hf i)
  unfold pot
  rw [Finset.prod_congr rfl (fun k _ => hk k), Finset.prod_mul_distrib, Finset.prod_ite_eq' univ j,
    if_pos (Finset.mem_univ j)]

end ReciprocityTheory.ReducedBases.T2

end
