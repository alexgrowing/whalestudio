import Mathlib
open Matrix Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder MatrixOrder

namespace GlobalTheory.MinorInt

theorem star_dot_self_re {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    (star x ⬝ᵥ x).re = ∑ i, ‖x i‖ ^ 2 := by
  rw [dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']
  norm_cast

theorem form_gram_re {ι κ : Type*} [Fintype ι] [Fintype κ] (B : Matrix κ ι ℂ) (x : ι → ℂ) :
    (star x ⬝ᵥ (Bᴴ * B) *ᵥ x).re = ∑ k, ‖(B *ᵥ x) k‖ ^ 2 := by
  rw [← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, star_dot_self_re]

theorem volume_ellipsoid_le {ι : Type*} [Fintype ι] [DecidableEq ι] (R : ℝ) {H : Matrix ι ι ℂ}
    (hH : H.PosSemidef) (hd : H.det ≠ 0) :
    volume {x : ι → ℂ | (star x ⬝ᵥ H *ᵥ x).re ≤ R} ≤
      ENNReal.ofReal ‖H.det‖⁻¹ * volume (Metric.closedBall (0 : ι → ℂ) (Real.sqrt R)) := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  have hB' : H = Bᴴ * B := hB
  have hdG : ‖H.det‖ = Complex.normSq B.det := by
    rw [hB', det_mul, det_conjTranspose, norm_mul, norm_star, Complex.normSq_eq_norm_sq, sq]
  have hpos : 0 < Complex.normSq B.det := hdG ▸ norm_pos_iff.mpr hd
  have hdet : LinearMap.det ((Matrix.toLin' B).restrictScalars ℝ) = Complex.normSq B.det := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]
  have := Measure.addHaar_preimage_linearMap (volume : Measure (ι → ℂ))
    (f := (Matrix.toLin' B).restrictScalars ℝ) (by rw [hdet]; exact hpos.ne')
    (Metric.closedBall (0 : ι → ℂ) (Real.sqrt R))
  rw [hdet, abs_of_pos (inv_pos.mpr hpos), ← hdG] at this
  rw [← this]
  refine measure_mono fun x hx => ?_
  simp only [Set.mem_setOf_eq, hB', form_gram_re] at hx
  simp only [Set.mem_preimage, mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun k => ?_
  refine Real.le_sqrt_of_sq_le (le_trans ?_ hx)
  exact Finset.single_le_sum (f := fun k => ‖(B *ᵥ x) k‖ ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ k)

theorem near_one (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ G : Matrix ι ι ℂ, (∀ i j, ‖(G - 1) i j‖ < δ) →
      1 / 2 ≤ ‖G.det‖ ∧ 1 / 2 ≤ ‖(1 - (2 : ℂ) • G).det‖ ∧
        ∀ t : ι → ℂ, (∑ i, ‖t i‖ ^ 2) / 2 ≤ (star t ⬝ᵥ G *ᵥ t).re := by
  have h1 : ∀ᶠ E : ι → ι → ℂ in nhds 0, 1 / 2 < ‖(Matrix.of E + 1).det‖ := by
    have hc : Continuous fun E : ι → ι → ℂ => ‖(Matrix.of E + 1).det‖ := by
      refine Continuous.norm (Continuous.matrix_det ?_)
      exact Continuous.add continuous_id continuous_const
    refine hc.continuousAt.eventually (lt_mem_nhds ?_)
    have : Matrix.of (0 : ι → ι → ℂ) = 0 := rfl
    simp [this]; norm_num
  have h2 : ∀ᶠ E : ι → ι → ℂ in nhds 0, 1 / 2 < ‖(1 - (2 : ℂ) • (Matrix.of E + 1)).det‖ := by
    have hc : Continuous fun E : ι → ι → ℂ => ‖(1 - (2 : ℂ) • (Matrix.of E + 1)).det‖ := by
      refine Continuous.norm (Continuous.matrix_det ?_)
      have hc0 : Continuous fun E : ι → ι → ℂ => Matrix.of E + 1 :=
        Continuous.add continuous_id continuous_const
      exact continuous_const.sub (hc0.const_smul (2 : ℂ))
    refine hc.continuousAt.eventually (lt_mem_nhds ?_)
    have : Matrix.of (0 : ι → ι → ℂ) = 0 := rfl
    have h3 : (1 : Matrix ι ι ℂ) - (2 : ℂ) • (1 : Matrix ι ι ℂ) = -1 := by
      rw [two_smul]; abel
    simp only [this, zero_add, h3, det_neg]
    simp; norm_num
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (h1.and h2)
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  refine ⟨min (min (ε / 2) 1) (1 / (2 * (N + 1))), by positivity,
    (min_le_left _ _).trans (min_le_right _ _), fun G hG => ?_⟩
  have hE : dist (fun i j => (G - 1) i j) 0 < ε := by
    rw [dist_zero_right]
    refine lt_of_le_of_lt ?_ (half_lt_self hε)
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    exact (hG i j).le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hGE : Matrix.of (fun i j => (G - 1) i j) + 1 = G := by
    ext i j; simp
  have h := hball hE
  rw [hGE] at h
  refine ⟨h.1.le, h.2.le, fun t => ?_⟩
  have hsplit : star t ⬝ᵥ G *ᵥ t = star t ⬝ᵥ t + star t ⬝ᵥ (G - 1) *ᵥ t := by
    rw [sub_mulVec, one_mulVec, dotProduct_sub]; ring
  have hb : ‖star t ⬝ᵥ (G - 1) *ᵥ t‖ ≤ 1 / (2 * (N + 1)) * (∑ i, ‖t i‖) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum, dotProduct]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [mulVec, dotProduct, Finset.mul_sum, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, norm_mul, Pi.star_apply, norm_star]
    have := (hG i j).le.trans (min_le_right _ _)
    calc ‖t i‖ * (‖(G - 1) i j‖ * ‖t j‖) = ‖(G - 1) i j‖ * (‖t i‖ * ‖t j‖) := by ring
      _ ≤ _ := by gcongr
  have hcs : (∑ i, ‖t i‖) ^ 2 ≤ N * ∑ i, ‖t i‖ ^ 2 := by
    simpa [hN] using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖t i‖)
  have hS : 0 ≤ ∑ i, ‖t i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb2 : 1 / (2 * (N + 1)) * (∑ i, ‖t i‖) ^ 2 ≤ (∑ i, ‖t i‖ ^ 2) / 2 := by
    rw [one_div, inv_mul_le_iff₀ (by positivity)]
    nlinarith
  have hre := (Complex.abs_re_le_norm (star t ⬝ᵥ (G - 1) *ᵥ t))
  rw [hsplit, Complex.add_re, star_dot_self_re]
  have := neg_abs_le (star t ⬝ᵥ (G - 1) *ᵥ t).re
  linarith

theorem form_diff_re {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι ι ℂ) (C : Matrix κ ι ℂ)
    (t : ι → ℂ) : (star t ⬝ᵥ (Aᴴ * A - Cᴴ * C) *ᵥ t).re =
      ∑ k, ‖(A *ᵥ t) k‖ ^ 2 - ∑ k, ‖(C *ᵥ t) k‖ ^ 2 := by
  rw [sub_mulVec, dotProduct_sub, Complex.sub_re, form_gram_re, form_gram_re]

theorem det_ne_zero_of_form {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι ι ℂ) (C : Matrix κ ι ℂ)
    (h : ∀ t : ι → ℂ, (∑ i, ‖t i‖ ^ 2) / 2 ≤ (star t ⬝ᵥ (Aᴴ * A - Cᴴ * C) *ᵥ t).re) :
    A.det ≠ 0 := by
  intro h0
  obtain ⟨t, ht, hAt⟩ := exists_mulVec_eq_zero_iff.2 h0
  have h1 := h t
  rw [form_diff_re, hAt] at h1
  have h2 : 0 ≤ ∑ k, ‖(C *ᵥ t) k‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h3 : ∑ i, ‖t i‖ ^ 2 = 0 :=
    le_antisymm (by simp at h1; linarith) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  apply ht
  ext i
  have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 h3 i (Finset.mem_univ _)
  simpa using this

theorem re_dot_le {ι : Type*} [Fintype ι] (c : ℝ) (hc : 0 < c) (x y : ι → ℂ) :
    (star x ⬝ᵥ y).re ≤ c * ∑ i, ‖x i‖ ^ 2 + (∑ i, ‖y i‖ ^ 2) / (4 * c) := by
  rw [dotProduct, Complex.re_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => (Complex.re_le_norm _).trans ?_
  rw [norm_mul, Pi.star_apply, norm_star]
  have : ‖y i‖ ^ 2 / (4 * c) = c * (‖y i‖ / (2 * c)) ^ 2 := by field_simp; ring
  have h2 : ‖x i‖ * ‖y i‖ = c * (2 * ‖x i‖ * (‖y i‖ / (2 * c))) := by field_simp
  rw [this, h2, ← mul_add]
  gcongr
  nlinarith [sq_nonneg (‖x i‖ - ‖y i‖ / (2 * c))]

theorem neg_on_perp {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι ι ℂ) (C : Matrix κ ι ℂ) (hA : A.det ≠ 0)
    (h : ∀ t : ι → ℂ, (∑ i, ‖t i‖ ^ 2) / 2 ≤ (star t ⬝ᵥ (Aᴴ * A - Cᴴ * C) *ᵥ t).re)
    (b : ι → ℂ) (d : κ → ℂ) :
    ∑ a, ‖b a‖ ^ 2 ≤ 2 * ∑ i, ‖(Aᴴ *ᵥ b - Cᴴ *ᵥ d) i‖ ^ 2 + ∑ c, ‖d c‖ ^ 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, b = A *ᵥ t :=
    ⟨A⁻¹ *ᵥ b, by rw [mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit hA), one_mulVec]⟩
  have h1 := h t
  rw [form_diff_re] at h1
  have key : star (A *ᵥ t) ⬝ᵥ (A *ᵥ t) =
      star (Aᴴ *ᵥ (A *ᵥ t) - Cᴴ *ᵥ d) ⬝ᵥ t + star d ⬝ᵥ (C *ᵥ t) := by
    rw [star_sub, sub_dotProduct, star_mulVec Aᴴ, star_mulVec Cᴴ, conjTranspose_conjTranspose,
      conjTranspose_conjTranspose, ← dotProduct_mulVec, ← dotProduct_mulVec]
    ring
  have h2 := congrArg Complex.re key
  rw [star_dot_self_re, Complex.add_re] at h2
  have h3 := re_dot_le 1 one_pos (Aᴴ *ᵥ (A *ᵥ t) - Cᴴ *ᵥ d) t
  have h4 := re_dot_le (1 / 2) (by norm_num) d (C *ᵥ t)
  rw [show (4 : ℝ) * (1 / 2) = 2 by norm_num] at h4
  rw [mul_one, one_mul] at h3
  linarith

theorem slice_volume (ι κ : Type*) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K : ENNReal, K < ⊤ ∧ ∀ (A : Matrix ι ι ℂ) (C : Matrix κ ι ℂ),
      (∀ i j, ‖(Aᴴ * A - Cᴴ * C - 1 : Matrix ι ι ℂ) i j‖ < δ) →
      volume {v : ι ⊕ κ → ℂ | (∀ i, ‖(Aᴴ *ᵥ (v ∘ Sum.inl) - Cᴴ *ᵥ (v ∘ Sum.inr)) i‖ ≤ 1) ∧
        ∑ c, ‖v (Sum.inr c)‖ ^ 2 - ∑ a, ‖v (Sum.inl a)‖ ^ 2 ≤ 2} ≤ K := by
  obtain ⟨δ, hδ, -, hnear⟩ := near_one ι
  set R : ℝ := 2 + 2 * (Fintype.card ι : ℝ) with hR
  refine ⟨δ, hδ, ENNReal.ofReal 2 * volume (Metric.closedBall (0 : ι ⊕ κ → ℂ) (Real.sqrt R)),
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top, fun A C hAC => ?_⟩
  obtain ⟨-, hd2, hform⟩ := hnear _ hAC
  have hA := det_ne_zero_of_form A C hform
  set J : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ := fromBlocks 1 0 0 (-1) with hJ
  set M : Matrix ι (ι ⊕ κ) ℂ := fromCols Aᴴ (-Cᴴ) with hM
  set H : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ := (2 : ℂ) • (Mᴴ * M) - J with hH
  have hMv : ∀ v : ι ⊕ κ → ℂ, M *ᵥ v = Aᴴ *ᵥ (v ∘ Sum.inl) - Cᴴ *ᵥ (v ∘ Sum.inr) := by
    intro v
    rw [hM, fromCols_mulVec, neg_mulVec, sub_eq_add_neg]
  have hJv : ∀ v : ι ⊕ κ → ℂ, (star v ⬝ᵥ J *ᵥ v).re =
      ∑ a, ‖v (Sum.inl a)‖ ^ 2 - ∑ c, ‖v (Sum.inr c)‖ ^ 2 := by
    intro v
    have h1 := star_dot_self_re (v ∘ Sum.inl)
    have h2 := star_dot_self_re (v ∘ Sum.inr)
    simp only [Function.comp_apply] at h1 h2
    rw [← h1, ← h2, hJ, fromBlocks_mulVec]
    simp [dotProduct, Fintype.sum_sum_type, neg_mulVec, sub_eq_add_neg]
  have hHv : ∀ v : ι ⊕ κ → ℂ, (star v ⬝ᵥ H *ᵥ v).re =
      2 * ∑ i, ‖(M *ᵥ v) i‖ ^ 2 - (∑ a, ‖v (Sum.inl a)‖ ^ 2 - ∑ c, ‖v (Sum.inr c)‖ ^ 2) := by
    intro v
    rw [hH, sub_mulVec, dotProduct_sub, Complex.sub_re, hJv, smul_mulVec, dotProduct_smul,
      smul_eq_mul, ← form_gram_re]
    simp
  have hherm : H.IsHermitian := by
    refine IsHermitian.sub ?_ ?_
    · unfold IsHermitian
      rw [conjTranspose_smul, (isHermitian_conjTranspose_mul_self M).eq]; simp
    · unfold IsHermitian
      rw [hJ, fromBlocks_conjTranspose]; simp
  have hpsd : H.PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg hherm fun v => ?_
    refine Complex.nonneg_iff.2 ⟨?_, (hherm.im_star_dotProduct_mulVec_self v).symm⟩
    rw [hHv, hMv]
    have := neg_on_perp A C hA hform (v ∘ Sum.inl) (v ∘ Sum.inr)
    simp only [Function.comp_apply] at this
    linarith
  have hJJ : J * J = 1 := by
    rw [hJ, fromBlocks_multiply]; simp [fromBlocks_one]
  have hdJ : ‖J.det‖ = 1 := by
    rw [hJ, det_fromBlocks_zero₂₁, det_neg]; simp
  have hdH : ‖H.det‖ = ‖(1 - (2 : ℂ) • (Aᴴ * A - Cᴴ * C)).det‖ := by
    have h1 : H = -J * (1 - (J * Mᴴ) * ((2 : ℂ) • M)) := by
      rw [hH, Matrix.mul_sub, Matrix.mul_one, Matrix.neg_mul, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, hJJ, Matrix.one_mul, Matrix.mul_smul]
      abel
    have h2 : M * (J * Mᴴ) = Aᴴ * A - Cᴴ * C := by
      rw [hM, hJ, conjTranspose_fromCols_eq_fromRows_conjTranspose, fromBlocks_mul_fromRows,
        fromCols_mul_fromRows]
      simp [sub_eq_add_neg]
    rw [h1, det_mul, det_one_sub_mul_comm, Matrix.smul_mul, h2, norm_mul, det_neg, norm_mul, hdJ]
    simp
  have hdH' : 1 / 2 ≤ ‖H.det‖ := hdH ▸ hd2
  have hne : H.det ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le (by norm_num) hdH')
  refine le_trans (measure_mono fun v hv => ?_) ((volume_ellipsoid_le R hpsd hne).trans ?_)
  · obtain ⟨hv1, hv2⟩ := hv
    show _ ≤ R
    rw [hHv, hMv]
    have : ∑ i, ‖(Aᴴ *ᵥ (v ∘ Sum.inl) - Cᴴ *ᵥ (v ∘ Sum.inr)) i‖ ^ 2 ≤ ∑ _i : ι, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ => by have := hv1 i; have := norm_nonneg ((Aᴴ *ᵥ (v ∘ Sum.inl) - Cᴴ *ᵥ (v ∘ Sum.inr)) i); nlinarith
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
    linarith
  · gcongr
    rw [inv_le_comm₀ (norm_pos_iff.2 hne) (by norm_num)]
    linarith

theorem lintegral_mul_right {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι ι ℂ) (hA : A.det ≠ 0) (F : (κ → ι → ℂ) → ENNReal) (hF : Measurable F) :
    ∫⁻ c, F c = ∫⁻ z : κ → ι → ℂ, ENNReal.ofReal (‖A.det‖ ^ (2 * Fintype.card κ)) *
      F (fun k => z k ᵥ* A) := by
  let L : (κ → ι → ℂ) →ₗ[ℂ] (κ → ι → ℂ) :=
    LinearMap.pi fun k => (Matrix.toLin' Aᵀ).comp (LinearMap.proj k)
  have hL : LinearMap.det L = A.det ^ Fintype.card κ := by
    rw [LinearMap.det_pi]; simp [LinearMap.det_toLin']
  have hdet : LinearMap.det (L.restrictScalars ℝ) = ‖A.det‖ ^ (2 * Fintype.card κ) := by
    rw [LinearMap.det_restrictScalars, hL, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq,
      norm_pow, ← pow_mul, mul_comm]
  have hpos : 0 < ‖A.det‖ ^ (2 * Fintype.card κ) := pow_pos (norm_pos_iff.2 hA) _
  haveI : (volume : Measure (κ → ι → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (κ → ι → ℂ))
    (f := L.restrictScalars ℝ) (by rw [hdet]; exact hpos.ne')
  have hm : Measurable (L.restrictScalars ℝ) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  have h1 := lintegral_map (μ := volume) hF hm
  rw [hmap, lintegral_smul_measure, hdet, abs_of_pos (inv_pos.2 hpos)] at h1
  have h2 : ∀ z : κ → ι → ℂ, (L.restrictScalars ℝ) z = fun k => z k ᵥ* A := by
    intro z; ext k i; simp [L, Matrix.toLin'_apply, mulVec_transpose]
  simp only [h2] at h1
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← h1, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ hpos.ne', ENNReal.ofReal_one, one_mul]

theorem weight_le {s u M : ℝ} (hs : 0 < s) (h : 1 / 2 ≤ s ^ 2 * u) (hM : u ≤ M) (p q k : ℕ) :
    s ^ (2 * q) * (s ^ (2 * (p + q) + k))⁻¹ ≤ (2 * u) ^ p * (1 + 2 * M) ^ k := by
  have h1 : s⁻¹ ^ 2 ≤ 2 * u := by
    rw [inv_pow, inv_le_iff_one_le_mul₀ (by positivity)]; linarith
  have h2 : s⁻¹ ≤ 1 + 2 * M := by nlinarith [sq_nonneg (s⁻¹ - 1), inv_pos.2 hs]
  have h3 : s ^ (2 * q) * (s ^ (2 * (p + q) + k))⁻¹ = (s⁻¹ ^ 2) ^ p * s⁻¹ ^ k := by
    simp only [inv_pow]; field_simp; ring
  rw [h3]
  have : 0 ≤ 2 * u := le_trans (by positivity) h1
  gcongr

theorem columns_integral (ι κ : Type*) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (n : ℕ) (hn : 2 * (Fintype.card ι + Fintype.card κ) ≤ n) :
    ∃ δ : ℝ, 0 < δ ∧ ∫⁻ x : (ι → ι → ℂ) × (κ → ι → ℂ),
      {x : (ι → ι → ℂ) × (κ → ι → ℂ) | ∀ i j, ‖((Matrix.of x.1)ᵀᴴ * (Matrix.of x.1)ᵀ -
        (Matrix.of x.2)ᴴ * Matrix.of x.2 - 1 : Matrix ι ι ℂ) i j‖ < δ}.indicator
        (fun x => ENNReal.ofReal (‖(Matrix.of x.1).det‖ ^ n)⁻¹) x < ⊤ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨δ, hδ, hδ1, hnear⟩ := near_one ι
  refine ⟨δ, hδ, ?_⟩
  set S := {x : (ι → ι → ℂ) × (κ → ι → ℂ) | ∀ i j, ‖((Matrix.of x.1)ᵀᴴ * (Matrix.of x.1)ᵀ -
        (Matrix.of x.2)ᴴ * Matrix.of x.2 - 1 : Matrix ι ι ℂ) i j‖ < δ} with hS
  have hSm : MeasurableSet S := by
    refine IsOpen.measurableSet ?_
    simp only [hS, Set.setOf_forall]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    refine isOpen_lt ?_ continuous_const
    simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, transpose_apply, of_apply]
    fun_prop
  have hdetc : Continuous fun a : ι → ι → ℂ => ‖(Matrix.of a).det‖ :=
    (Continuous.matrix_det continuous_id).norm
  set F : (ι → ι → ℂ) × (κ → ι → ℂ) → ENNReal := S.indicator
    (fun x => ENNReal.ofReal (‖(Matrix.of x.1).det‖ ^ (2 * (Fintype.card ι + Fintype.card κ) + k))⁻¹)
    with hF
  have hFm : Measurable F := by
    refine Measurable.indicator ?_ hSm
    exact (((hdetc.measurable.comp measurable_fst).pow_const _).inv).ennreal_ofReal
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z ∈ Metric.closedBall (0 : κ → ι → ℂ) 1,
      ‖(1 - (Matrix.of z)ᴴ * Matrix.of z : Matrix ι ι ℂ).det‖ ≤ M := by
    refine (isCompact_closedBall _ _).exists_bound_of_continuousOn (Continuous.continuousOn ?_)
    refine Continuous.matrix_det (continuous_const.sub ?_)
    have : Continuous fun z : κ → ι → ℂ => Matrix.of z := continuous_id
    exact this.matrix_conjTranspose.matrix_mul this
  set V := volume (Metric.closedBall (0 : ι → ℂ) (Real.sqrt 2)) with hV
  set K : ENNReal := ENNReal.ofReal (2 ^ Fintype.card ι * (1 + 2 * M) ^ k) * V ^ Fintype.card ι
    with hK
  have hKt : K < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.pow_lt_top measure_closedBall_lt_top)
  set T : (ι → ι → ℂ) → (κ → ι → ℂ) → ENNReal := fun a z =>
    ENNReal.ofReal (‖(Matrix.of a)ᵀ.det‖ ^ (2 * Fintype.card κ)) *
      F (a, fun c => z c ᵥ* (Matrix.of a)ᵀ) with hT
  have hTm : Measurable (Function.uncurry T) := by
    refine Measurable.mul ?_ (hFm.comp (Continuous.measurable ?_))
    · simp only [det_transpose]
      exact ((hdetc.measurable.comp measurable_fst).pow_const _).ennreal_ofReal
    · refine continuous_fst.prodMk (continuous_pi fun c => continuous_pi fun i => ?_)
      simp only [vecMul, dotProduct, transpose_apply, of_apply]
      fun_prop
  have step1 : ∀ a, ∫⁻ c, F (a, c) ≤ ∫⁻ z, T a z := by
    intro a
    by_cases ha : (Matrix.of a)ᵀ.det = 0
    · have : ∀ c, F (a, c) = 0 := fun c => Set.indicator_of_notMem
        (fun h : (a, c) ∈ S => det_ne_zero_of_form _ _ (hnear _ h).2.2 ha) _
      simp [this]
    · exact (lintegral_mul_right _ ha (fun c => F (a, c))
        (hFm.comp measurable_prodMk_left)).le
  have step2 : ∀ z, ∫⁻ a, T a z ≤ (Metric.closedBall (0 : κ → ι → ℂ) 1).indicator (fun _ => K) z := by
    intro z
    set P : Matrix ι ι ℂ := 1 - (Matrix.of z)ᴴ * Matrix.of z with hP
    have hG : ∀ a : ι → ι → ℂ, (Matrix.of a)ᵀᴴ * (Matrix.of a)ᵀ -
        (Matrix.of fun c => z c ᵥ* (Matrix.of a)ᵀ)ᴴ * (Matrix.of fun c => z c ᵥ* (Matrix.of a)ᵀ) =
        (Matrix.of a)ᵀᴴ * P * (Matrix.of a)ᵀ := by
      intro a
      have : (Matrix.of fun c => z c ᵥ* (Matrix.of a)ᵀ) = Matrix.of z * (Matrix.of a)ᵀ := rfl
      rw [this, hP, conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    have hdet : ∀ a : ι → ι → ℂ, (a, fun c => z c ᵥ* (Matrix.of a)ᵀ) ∈ S →
        1 / 2 ≤ ‖(Matrix.of a).det‖ ^ 2 * ‖P.det‖ := by
      intro a ha
      have := (hnear _ ha).1
      simp only [hG] at this
      rw [det_mul, det_mul, det_conjTranspose, det_transpose, norm_mul, norm_mul, norm_star] at this
      linarith
    by_cases hex : ∃ a : ι → ι → ℂ, (a, fun c => z c ᵥ* (Matrix.of a)ᵀ) ∈ S
    swap
    · have : ∀ a, T a z = 0 := fun a => by
        simp only [hT, hF]
        rw [Set.indicator_of_notMem (fun h => hex ⟨a, h⟩), mul_zero]
      simp [this]
    obtain ⟨a₀, ha₀⟩ := hex
    have hform := (hnear _ ha₀).2.2
    have hA₀ := det_ne_zero_of_form _ _ hform
    simp only [hG] at hform
    have hherm : P.IsHermitian := isHermitian_one.sub (isHermitian_conjTranspose_mul_self _)
    have hre : ∀ v, 0 ≤ (star v ⬝ᵥ P *ᵥ v).re := by
      intro v
      obtain ⟨t, rfl⟩ : ∃ t, v = (Matrix.of a₀)ᵀ *ᵥ t := ⟨(Matrix.of a₀)ᵀ⁻¹ *ᵥ v, by
        rw [mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit hA₀), one_mulVec]⟩
      have := hform t
      rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec] at this
      exact le_trans (by positivity) this
    have hpsd : P.PosSemidef := PosSemidef.of_dotProduct_mulVec_nonneg hherm fun v =>
      Complex.nonneg_iff.2 ⟨hre v, (hherm.im_star_dotProduct_mulVec_self v).symm⟩
    have hPpos : 0 < ‖P.det‖ := by
      refine lt_of_le_of_ne (norm_nonneg _) fun h => ?_
      have := hdet a₀ ha₀
      rw [← h] at this; norm_num at this
    have hz : z ∈ Metric.closedBall (0 : κ → ι → ℂ) 1 := by
      rw [mem_closedBall_zero_iff]
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun c => ?_
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
      have h1 := hre (Pi.single j 1)
      rw [hP, sub_mulVec, dotProduct_sub, Complex.sub_re, form_gram_re, one_mulVec,
        star_dot_self_re] at h1
      have h2 : ∑ i, ‖(Pi.single j (1 : ℂ) : ι → ℂ) i‖ ^ 2 = 1 := by
        rw [Finset.sum_eq_single j] <;> simp +contextual
      have h3 := Finset.single_le_sum (f := fun c => ‖(Matrix.of z *ᵥ Pi.single j 1) c‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ c)
      have h4 : (Matrix.of z *ᵥ Pi.single j 1) c = z c j := by simp
      simp only [h4] at h3
      have := norm_nonneg (z c j)
      nlinarith
    rw [Set.indicator_of_mem hz]
    have hMz : ‖P.det‖ ≤ M := hM z hz
    set E : Set (ι → ℂ) := {x | (star x ⬝ᵥ P *ᵥ x).re ≤ 2} with hE
    have hpt : ∀ a, T a z ≤ (Set.univ.pi fun _ : ι => E).indicator
        (fun _ => ENNReal.ofReal ((2 * ‖P.det‖) ^ Fintype.card ι * (1 + 2 * M) ^ k)) a := by
      intro a
      by_cases ha : (a, fun c => z c ᵥ* (Matrix.of a)ᵀ) ∈ S
      swap
      · simp only [hT, hF]
        rw [Set.indicator_of_notMem ha, mul_zero]; exact zero_le
      have hmem : a ∈ Set.univ.pi fun _ : ι => E := by
        intro j _
        have h1 := ha j j
        simp only [hG] at h1
        have h2 : ((Matrix.of a)ᵀᴴ * P * (Matrix.of a)ᵀ) j j = star (a j) ⬝ᵥ P *ᵥ a j := by
          rw [Matrix.mul_assoc]; rfl
        rw [Matrix.sub_apply, h2, one_apply_eq] at h1
        have h3 := Complex.re_le_norm (star (a j) ⬝ᵥ P *ᵥ a j - 1)
        rw [Complex.sub_re, Complex.one_re] at h3
        show _ ≤ (2 : ℝ)
        linarith
      simp only [hT, hF]
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem ha, ← ENNReal.ofReal_mul (by positivity),
        det_transpose]
      refine ENNReal.ofReal_le_ofReal (weight_le ?_ (hdet a ha) hMz _ _ _)
      have := det_ne_zero_of_form _ _ (hnear _ ha).2.2
      rw [det_transpose] at this
      exact norm_pos_iff.2 this
    refine (lintegral_mono hpt).trans ((lintegral_indicator_const_le _ _).trans ?_)
    rw [volume_pi_pi, Finset.prod_const, Finset.card_univ]
    have hvol := volume_ellipsoid_le 2 hpsd (norm_pos_iff.1 hPpos)
    have hM0 : 0 ≤ M := hPpos.le.trans hMz
    refine (mul_le_mul_right (pow_le_pow_left' hvol _) _).trans (le_of_eq ?_)
    rw [hK, mul_pow (ENNReal.ofReal _), ← mul_assoc, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [mul_pow, inv_pow]
    field_simp
  calc ∫⁻ x, F x = ∫⁻ a, ∫⁻ c, F (a, c) := lintegral_prod _ hFm.aemeasurable
    _ ≤ ∫⁻ a, ∫⁻ z, T a z := lintegral_mono step1
    _ = ∫⁻ z, ∫⁻ a, T a z := lintegral_lintegral_swap hTm.aemeasurable
    _ ≤ _ := lintegral_mono step2
    _ ≤ K * volume (Metric.closedBall (0 : κ → ι → ℂ) 1) := lintegral_indicator_const_le _ _
    _ < ⊤ := ENNReal.mul_lt_top hKt measure_closedBall_lt_top

noncomputable def cutEquiv (ι κ : Type*) :
    (ι ⊕ κ → ι ⊕ κ → ℂ) ≃ₗ[ℝ] ((ι → ι → ℂ) × (κ → ι → ℂ)) × (κ → ι ⊕ κ → ℂ) where
  toFun y := ((fun j a => conj (y (Sum.inl a) (Sum.inl j)),
    fun c j => conj (y (Sum.inr c) (Sum.inl j))), fun c r => conj (y r (Sum.inr c)))
  invFun x := fun r s => Sum.elim
    (fun j => Sum.elim (fun a => conj (x.1.1 j a)) (fun c => conj (x.1.2 c j)) r)
    (fun c => conj (x.2 c r)) s
  map_add' y y' := by ext <;> simp
  map_smul' t y := by ext <;> simp
  left_inv y := by ext r s; rcases r with r | r <;> rcases s with s | s <;> simp
  right_inv x := by ext <;> simp

theorem lintegral_cutEquiv (ι κ : Type*) [Fintype ι] [Fintype κ] :
    ∃ c : ENNReal, c < ⊤ ∧ ∀ g : ((ι → ι → ℂ) × (κ → ι → ℂ)) × (κ → ι ⊕ κ → ℂ) → ENNReal,
      ∫⁻ y, g (cutEquiv ι κ y) = c * ∫⁻ w, g w := by
  let e := (cutEquiv ι κ).toContinuousLinearEquiv
  haveI : BorelSpace (ι → ι → ℂ) := Pi.borelSpace
  haveI : BorelSpace (κ → ι → ℂ) := Pi.borelSpace
  haveI : BorelSpace (κ → ι ⊕ κ → ℂ) := Pi.borelSpace
  haveI : BorelSpace (ι ⊕ κ → ι ⊕ κ → ℂ) := Pi.borelSpace
  haveI : BorelSpace ((ι → ι → ℂ) × (κ → ι → ℂ)) := Prod.borelSpace
  haveI : BorelSpace (((ι → ι → ℂ) × (κ → ι → ℂ)) × (κ → ι ⊕ κ → ℂ)) := Prod.borelSpace
  haveI : (volume : Measure (ι → ι → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (κ → ι → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (κ → ι ⊕ κ → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (ι ⊕ κ → ι ⊕ κ → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure ((ι → ι → ℂ) × (κ → ι → ℂ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  haveI : (volume : Measure (((ι → ι → ℂ) × (κ → ι → ℂ)) × (κ → ι ⊕ κ → ℂ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hmap := Measure.isAddLeftInvariant_eq_smul (Measure.map e volume)
    (volume : Measure (((ι → ι → ℂ) × (κ → ι → ℂ)) × (κ → ι ⊕ κ → ℂ)))
  refine ⟨Measure.addHaarScalarFactor (Measure.map e volume) volume, ENNReal.coe_lt_top,
    fun g => ?_⟩
  have hchg : ∫⁻ y, g (e y) = ∫⁻ w, g w ∂(Measure.map e volume) :=
    (lintegral_map_equiv g e.toHomeomorph.toMeasurableEquiv).symm
  refine hchg.trans ?_
  conv_lhs => rw [hmap]
  rw [lintegral_smul_measure]
  rfl

theorem integrableOn_minor (ι κ : Type*) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (n : ℕ) (hn : 2 * (Fintype.card ι + Fintype.card κ) ≤ n) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ IntegrableOn
      (fun y : (ι ⊕ κ) → (ι ⊕ κ) → ℂ => (‖(Matrix.of y).toBlocks₁₁.det‖ ^ n)⁻¹)
      {y | ∀ a b, ‖((Matrix.of y)ᵀ * Matrix.fromBlocks (1 : Matrix ι ι ℂ) 0 0 (-1 : Matrix κ κ ℂ) *
        (Matrix.of y).map conj - Matrix.fromBlocks (1 : Matrix ι ι ℂ) 0 0 (-1 : Matrix κ κ ℂ)) a b‖
          < δ₀} volume := by
  obtain ⟨δ₁, hδ₁, K, hK, hslice⟩ := slice_volume ι κ
  obtain ⟨δ₂, hδ₂, hint⟩ := columns_integral ι κ n hn
  refine ⟨min (min δ₁ δ₂) 1, by positivity, ?_⟩
  set U := {y : (ι ⊕ κ) → (ι ⊕ κ) → ℂ | ∀ a b, ‖((Matrix.of y)ᵀ *
    Matrix.fromBlocks (1 : Matrix ι ι ℂ) 0 0 (-1 : Matrix κ κ ℂ) *
        (Matrix.of y).map conj - Matrix.fromBlocks (1 : Matrix ι ι ℂ) 0 0 (-1 : Matrix κ κ ℂ)) a b‖
          < min (min δ₁ δ₂) 1} with hU
  have hent : ∀ (y : (ι ⊕ κ) → (ι ⊕ κ) → ℂ) r s, ((Matrix.of y)ᵀ *
      Matrix.fromBlocks (1 : Matrix ι ι ℂ) 0 0 (-1 : Matrix κ κ ℂ) * (Matrix.of y).map conj) r s =
      ∑ a, y (Sum.inl a) r * conj (y (Sum.inl a) s) -
        ∑ c, y (Sum.inr c) r * conj (y (Sum.inr c) s) := by
    intro y r s
    rw [Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_sum_type]
    simp [Matrix.mul_apply, Fintype.sum_sum_type, one_apply, sub_eq_add_neg, neg_ite]
  have hUm : MeasurableSet U := by
    refine IsOpen.measurableSet ?_
    simp only [hU, Set.setOf_forall, Matrix.sub_apply, hent]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    refine isOpen_lt ?_ continuous_const
    fun_prop
  have hfm : Measurable fun y : (ι ⊕ κ) → (ι ⊕ κ) → ℂ =>
      (‖(Matrix.of y).toBlocks₁₁.det‖ ^ n)⁻¹ := by
    refine ((Continuous.measurable (Continuous.norm (Continuous.matrix_det ?_))).pow_const _).inv
    exact continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply (Sum.inl j)).comp (continuous_apply (Sum.inl i))
  refine ⟨hfm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun y => by positivity),
    ← lintegral_indicator hUm]
  set S := {x : (ι → ι → ℂ) × (κ → ι → ℂ) | ∀ i j, ‖((Matrix.of x.1)ᵀᴴ * (Matrix.of x.1)ᵀ -
        (Matrix.of x.2)ᴴ * Matrix.of x.2 - 1 : Matrix ι ι ℂ) i j‖ < min δ₁ δ₂} with hS
  set B : (ι → ι → ℂ) × (κ → ι → ℂ) → Set (ι ⊕ κ → ℂ) := fun x =>
    {v | (∀ i, ‖((Matrix.of x.1)ᵀᴴ *ᵥ (v ∘ Sum.inl) - (Matrix.of x.2)ᴴ *ᵥ (v ∘ Sum.inr)) i‖ ≤ 1) ∧
        ∑ c, ‖v (Sum.inr c)‖ ^ 2 - ∑ a, ‖v (Sum.inl a)‖ ^ 2 ≤ 2} with hB
  set g : ((ι → ι → ℂ) × (κ → ι → ℂ)) × (κ → ι ⊕ κ → ℂ) → ENNReal := fun w =>
    (Set.univ.pi fun _ : κ => B w.1).indicator
      (fun _ => S.indicator (fun x => ENNReal.ofReal (‖(Matrix.of x.1).det‖ ^ n)⁻¹) w.1) w.2 with hg
  let e := cutEquiv ι κ
  have hpt : ∀ y, U.indicator
      (fun y => ENNReal.ofReal (‖(Matrix.of y).toBlocks₁₁.det‖ ^ n)⁻¹) y ≤ g (e y) := by
    intro y
    by_cases hy : y ∈ U
    swap
    · rw [Set.indicator_of_notMem hy]; exact zero_le
    have hy' : ∀ r s, ‖∑ a, y (Sum.inl a) r * conj (y (Sum.inl a) s) -
        ∑ c, y (Sum.inr c) r * conj (y (Sum.inr c) s) -
        Matrix.fromBlocks (1 : Matrix ι ι ℂ) 0 0 (-1 : Matrix κ κ ℂ) r s‖ < min (min δ₁ δ₂) 1 := by
      intro r s
      have := hy r s
      rwa [Matrix.sub_apply, hent] at this
    have h1 : (e y).1 ∈ S := by
      intro i j
      refine lt_of_eq_of_lt ?_ ((hy' (Sum.inl i) (Sum.inl j)).trans_le (min_le_left _ _))
      simp [e, cutEquiv, Matrix.mul_apply]
    have h2 : (e y).2 ∈ Set.univ.pi fun _ : κ => B (e y).1 := by
      intro c _
      refine ⟨fun i => ?_, ?_⟩
      · refine le_of_eq_of_le ?_ ((hy' (Sum.inl i) (Sum.inr c)).le.trans (min_le_right _ _))
        simp [e, cutEquiv, mulVec, dotProduct]
      · have h3 := (hy' (Sum.inr c) (Sum.inr c)).le.trans (min_le_right _ _)
        have h4 := (Complex.abs_re_le_norm _).trans h3
        simp only [Complex.mul_conj', fromBlocks_apply₂₂, Matrix.neg_apply, one_apply_eq,
          ← Complex.ofReal_pow, ← Complex.ofReal_sum, Complex.sub_re, Complex.ofReal_re,
          Complex.neg_re, Complex.one_re] at h4
        have h5 := (abs_le.1 h4).1
        have : ∀ r, ‖(e y).2 c r‖ = ‖y r (Sum.inr c)‖ := fun r => by simp [e, cutEquiv]
        simp only [this]
        linarith
    simp only [hg]
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem h2, Set.indicator_of_mem h1]
    have h6 : Matrix.of (e y).1.1 = (Matrix.of y).toBlocks₁₁ᴴ := by
      ext i j; simp [e, cutEquiv, toBlocks₁₁]
    rw [h6, det_conjTranspose, norm_star]
  obtain ⟨c, hc, hchg⟩ := lintegral_cutEquiv ι κ
  refine (lintegral_mono hpt).trans_lt ?_
  refine (hchg g).trans_lt (ENNReal.mul_lt_top hc ?_)
  refine (lintegral_prod_le g).trans_lt ?_
  have hKt : K ^ Fintype.card κ < ⊤ := ENNReal.pow_lt_top hK
  refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top hint hKt)
  rw [← lintegral_mul_const' _ _ hKt.ne]
  refine lintegral_mono fun x => (lintegral_indicator_const_le (Set.univ.pi fun _ : κ => B x)
    (S.indicator (fun x => ENNReal.ofReal (‖(Matrix.of x.1).det‖ ^ n)⁻¹) x)).trans ?_
  by_cases hx : x ∈ S
  swap
  · simp only [Set.indicator_of_notMem hx, zero_mul]; exact zero_le
  rw [volume_pi_pi, Finset.prod_const, Finset.card_univ]
  refine mul_le_mul' ?_ (pow_le_pow_left'
    (hslice _ _ fun i j => (hx i j).trans_le (min_le_left _ _)) _)
  exact Set.indicator_le_indicator_of_subset
    (fun x hx i j => (hx i j).trans_le (min_le_right _ _)) (fun _ => zero_le) x

end GlobalTheory.MinorInt
