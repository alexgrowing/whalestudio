import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsLinearIndependentNormLeSuccMin
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsLinearIndependentSqrtEqSuccMinQuad

noncomputable section

open Module Submodule
open scoped InnerProductSpace

namespace GlobalTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_add_orthogonal_norm_sq_le (W : Submodule ℝ E) (u : E) :
    ∃ p ∈ W, ∃ q ∈ Wᗮ, u = p + q ∧ ‖q‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  obtain ⟨p, hp, q, hq, h⟩ := W.exists_add_mem_mem_orthogonal u
  refine ⟨p, hp, q, hq, h, ?_⟩
  rw [h, norm_add_sq_real, Submodule.inner_right_of_mem_orthogonal hp hq]
  nlinarith [sq_nonneg ‖p‖]

theorem exists_mem_span_int_norm_sub_sq_le_sum {ι : Type*} (v : ι → E) (s : Finset ι) {x : E}
    (hx : x ∈ span ℝ (v '' s)) :
    ∃ w ∈ span ℤ (v '' s), ‖x - w‖ ^ 2 ≤ (1 / 4) * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty =>
    refine ⟨0, zero_mem _, ?_⟩
    have : x = 0 := by simpa using hx
    simp [this]
  | insert a s ha ih =>
    rw [Finset.coe_insert, Set.image_insert_eq] at hx ⊢
    obtain ⟨t, y, hy, rfl⟩ := mem_span_insert.1 hx
    obtain ⟨p, hp, q, hq, hv, hle⟩ := exists_add_orthogonal_norm_sq_le (span ℝ (v '' s)) (v a)
    have hy' : y + (t - round t) • p ∈ span ℝ (v '' s) := add_mem hy (smul_mem _ _ hp)
    obtain ⟨w, hw, hwle⟩ := ih hy'
    have hwR : w ∈ span ℝ (v '' s) := span_subset_span ℤ ℝ _ hw
    refine ⟨round t • v a + w, mem_span_insert.2 ⟨_, _, hw, rfl⟩, ?_⟩
    have he : t • v a + y - (round t • v a + w) =
        (y + (t - round t) • p - w) + (t - round t) • q := by
      rw [← Int.cast_smul_eq_zsmul ℝ, hv]; module
    rw [he, norm_add_sq_real,
      Submodule.inner_right_of_mem_orthogonal (sub_mem hy' hwR) (smul_mem _ _ hq),
      Finset.sum_insert ha, norm_smul, mul_pow, Real.norm_eq_abs]
    have h1 : |t - round t| ^ 2 ≤ 1 / 4 := by
      have := pow_le_pow_left₀ (abs_nonneg _) (abs_sub_round t) 2
      linarith
    nlinarith [mul_le_mul h1 hle (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 4)]

theorem exists_short_generator_inf_span_insert (L : Submodule ℤ E) [DiscreteTopology L]
    {ι : Type*} (v : ι → E) (s : Finset ι) (hv : ∀ i ∈ s, v i ∈ L) {u : E} (huL : u ∈ L)
    (hu : u ∉ span ℝ (v '' s)) :
    ∃ b : E, L ⊓ (span ℝ (insert u (v '' s))).restrictScalars ℤ =
        span ℤ {b} ⊔ L ⊓ (span ℝ (v '' s)).restrictScalars ℤ ∧
      ‖b‖ ^ 2 ≤ ‖u‖ ^ 2 + (1 / 4) * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  set W := span ℝ (v '' s) with hW
  set C := ‖u‖ ^ 2 + (1 / 4) * ∑ i ∈ s, ‖v i‖ ^ 2 with hC
  obtain ⟨p, hp, q, hq, hupq, hle⟩ := exists_add_orthogonal_norm_sq_le W u
  have hZ : span ℤ (v '' s) ≤ L := span_le.2 (by rintro _ ⟨i, hi, rfl⟩; exact hv i hi)

  have red : ∀ (t : ℝ) (y : E), y ∈ W → t • u + y ∈ L → 0 < t → t ≤ 1 →
      ∃ y' ∈ W, t • u + y' ∈ L ∧ ‖t • u + y'‖ ^ 2 ≤ C := by
    intro t y hy hL h0 h1
    have hy' : y + t • p ∈ W := add_mem hy (smul_mem _ _ hp)
    obtain ⟨w, hw, hwle⟩ := exists_mem_span_int_norm_sub_sq_le_sum v s hy'
    have hwR : w ∈ W := span_subset_span ℤ ℝ _ hw
    refine ⟨y - w, sub_mem hy hwR, by rw [← add_sub_assoc]; exact sub_mem hL (hZ hw), ?_⟩
    have he : t • u + (y - w) = (y + t • p - w) + t • q := by rw [hupq]; module
    rw [he, norm_add_sq_real,
      Submodule.inner_right_of_mem_orthogonal (sub_mem hy' hwR) (smul_mem _ _ hq),
      norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have h2 : t ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul h2 hle (sq_nonneg _) zero_le_one]

  have uniq : ∀ (t t' : ℝ) (y y' : E), y ∈ W → y' ∈ W → t • u + y = t' • u + y' → t = t' := by
    intro t t' y y' hy hy' h
    by_contra hne
    apply hu
    have : u = (t - t')⁻¹ • (y' - y) := by
      rw [eq_inv_smul_iff₀ (sub_ne_zero.2 hne), sub_smul, sub_eq_sub_iff_add_eq_add, h, add_comm]
    rw [this]; exact smul_mem _ _ (sub_mem hy' hy)
  let T : Set ℝ := {t | 0 < t ∧ t ≤ 1 ∧ ∃ y ∈ W, t • u + y ∈ L ∧ ‖t • u + y‖ ^ 2 ≤ C}
  have hT : T.Finite := by
    choose! f hfW hfL hfC using fun (t : ℝ) (ht : t ∈ T) => ht.2.2
    refine Set.Finite.of_injOn (f := fun t => t • u + f t) ?_ ?_ (finite_mem_and_norm_le L √C)
    · exact fun t ht => ⟨hfL t ht, Real.le_sqrt_of_sq_le (hfC t ht)⟩
    · exact fun t ht t' ht' h => uniq _ _ _ _ (hfW t ht) (hfW t' ht') h
  have hT1 : (1 : ℝ) ∈ T :=
    ⟨one_pos, le_rfl, red 1 0 (zero_mem _) (by simpa using huL) one_pos le_rfl⟩
  obtain ⟨t₀, ⟨h0, h1, y₀, hy₀, hbL, hbC⟩, hmin⟩ := Set.exists_min_image T id hT ⟨1, hT1⟩
  refine ⟨t₀ • u + y₀, le_antisymm ?_ (sup_le ?_ ?_), hbC⟩
  · rintro x ⟨hxL, hx⟩
    obtain ⟨t, y, hy, rfl⟩ := mem_span_insert.1 hx
    set k : ℤ := ⌊t / t₀⌋ with hk
    have hk1 : k * t₀ ≤ t := (le_div_iff₀ h0).1 (Int.floor_le _)
    have hk2 : t < (k + 1) * t₀ := (div_lt_iff₀ h0).1 (Int.lt_floor_add_one _)
    have he : t • u + y - k • (t₀ • u + y₀) = (t - k * t₀) • u + (y - (k : ℝ) • y₀) := by
      rw [← Int.cast_smul_eq_zsmul ℝ]; module
    have hyW : y - (k : ℝ) • y₀ ∈ W := sub_mem hy (smul_mem _ _ hy₀)
    have hL' : (t - k * t₀) • u + (y - (k : ℝ) • y₀) ∈ L := he ▸ sub_mem hxL (smul_mem _ _ hbL)
    have hz : t - k * t₀ = 0 := by
      by_contra hne
      have hpos : 0 < t - k * t₀ := lt_of_le_of_ne (by linarith) (Ne.symm hne)
      have hlt : t - k * t₀ < t₀ := by linarith
      exact absurd (hmin _ ⟨hpos, by linarith, red _ _ hyW hL' hpos (by linarith)⟩) (not_le.2 hlt)
    rw [hz, zero_smul, zero_add] at he hL'
    rw [eq_add_of_sub_eq' he]
    exact add_mem (mem_sup_left (smul_mem _ _ (mem_span_singleton_self _)))
      (mem_sup_right ⟨hL', hyW⟩)
  · rw [span_singleton_le_iff_mem]
    exact ⟨hbL, mem_span_insert.2 ⟨_, _, hy₀, rfl⟩⟩
  · exact inf_le_inf_left _ fun x hx => span_mono (Set.subset_insert _ _) hx

theorem exists_short_family_adapted (L : Submodule ℤ E) [DiscreteTopology L] {n : ℕ}
    {v : Fin n → E} (hv : LinearIndependent ℝ v) (hL : ∀ i, v i ∈ L) :
    ∃ b : Fin n → E, LinearIndependent ℝ b ∧
      (∀ s : ℕ, span ℤ (b '' {i : Fin n | (i : ℕ) < s}) =
        L ⊓ (span ℝ (v '' {i : Fin n | (i : ℕ) < s})).restrictScalars ℤ) ∧
      ∀ i, ‖b i‖ ^ 2 ≤ ‖v i‖ ^ 2 + (1 / 4) * ∑ j ∈ Finset.Iio i, ‖v j‖ ^ 2 := by
  choose b hb hbn using fun i : Fin n => exists_short_generator_inf_span_insert L v
    (Finset.Iio i) (fun j _ => hL j) (hL i) (hv.notMem_span_image (by simp))
  have key : ∀ s : ℕ, span ℤ (b '' {i : Fin n | (i : ℕ) < s}) =
      L ⊓ (span ℝ (v '' {i : Fin n | (i : ℕ) < s})).restrictScalars ℤ := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      by_cases hs : s < n
      · have h1 : {i : Fin n | (i : ℕ) < s + 1} = insert ⟨s, hs⟩ {i : Fin n | (i : ℕ) < s} := by
          ext i; simp [Fin.ext_iff]; omega
        have h2 : ((Finset.Iio (⟨s, hs⟩ : Fin n) : Finset (Fin n)) : Set (Fin n)) =
            {i : Fin n | (i : ℕ) < s} := by
          ext i; simp [Fin.lt_def]
        have h3 := hb ⟨s, hs⟩
        rw [h2] at h3
        rw [h1, Set.image_insert_eq, Set.image_insert_eq, h3, span_insert, ih]
      · have h1 : {i : Fin n | (i : ℕ) < s + 1} = {i : Fin n | (i : ℕ) < s} := by
          ext i; have := i.2; simp; omega
        rw [h1, ih]
  refine ⟨b, ?_, key, hbn⟩
  have hu : {i : Fin n | (i : ℕ) < n} = Set.univ := by ext i; simp
  have h := key n
  rw [hu, Set.image_univ, Set.image_univ] at h
  have hsp : span ℝ (Set.range b) = span ℝ (Set.range v) := by
    refine le_antisymm (span_le.2 fun x hx => ?_) (span_le.2 ?_)
    · exact (h.le (subset_span hx)).2
    · rintro _ ⟨i, rfl⟩
      exact span_subset_span ℤ ℝ _ (h.ge ⟨hL i, subset_span ⟨i, rfl⟩⟩)
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hsp, finrank_span_eq_card hv]

theorem exists_short_basis_adapted_of_subset_span (L : Submodule ℤ E) [DiscreteTopology L] {n : ℕ}
    {v : Fin n → E} (hv : LinearIndependent ℝ v) (hL : ∀ i, v i ∈ L)
    (hspan : (L : Set E) ⊆ span ℝ (Set.range v)) :
    ∃ b : Basis (Fin n) ℤ L,
      (∀ s : ℕ, span ℤ ((fun i => (b i : E)) '' {i : Fin n | (i : ℕ) < s}) =
        L ⊓ (span ℝ (v '' {i : Fin n | (i : ℕ) < s})).restrictScalars ℤ) ∧
      ∀ i, ‖(b i : E)‖ ^ 2 ≤ ‖v i‖ ^ 2 + (1 / 4) * ∑ j ∈ Finset.Iio i, ‖v j‖ ^ 2 := by
  obtain ⟨b, hb, hflag, hn⟩ := exists_short_family_adapted L hv hL
  have hu : {i : Fin n | (i : ℕ) < n} = Set.univ := by ext i; simp
  have h := hflag n
  rw [hu, Set.image_univ, Set.image_univ, inf_eq_left.2 (show L ≤ _ from hspan)] at h
  have hbZ : LinearIndependent ℤ b := hb.restrict_scalars' ℤ
  have hc : ∀ i, (((Basis.span hbZ).map (LinearEquiv.ofEq _ _ h) i : L) : E) = b i := by
    intro i; simp
  refine ⟨(Basis.span hbZ).map (LinearEquiv.ofEq _ _ h), ?_, ?_⟩
  · simpa only [hc] using hflag
  · simpa only [hc] using hn

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in

theorem norm_sq_add_sum_Iio_le {n : ℕ} {v : Fin n → E} {i : Fin n} {r : ℝ}
    (h : ∀ j ≤ i, ‖v j‖ ≤ r) :
    ‖v i‖ ^ 2 + (1 / 4) * ∑ j ∈ Finset.Iio i, ‖v j‖ ^ 2 ≤ (((i : ℕ) + 1 + 3 : ℝ) / 4) * r ^ 2 := by
  have h1 : ∑ j ∈ Finset.Iio i, ‖v j‖ ^ 2 ≤ (Finset.Iio i).card • r ^ 2 :=
    Finset.sum_le_card_nsmul _ _ _ fun j hj =>
      pow_le_pow_left₀ (norm_nonneg _) (h j (Finset.mem_Iio.1 hj).le) 2
  rw [Fin.card_Iio, nsmul_eq_mul] at h1
  have h2 := pow_le_pow_left₀ (norm_nonneg _) (h i le_rfl) 2
  linarith

end GlobalTheory
