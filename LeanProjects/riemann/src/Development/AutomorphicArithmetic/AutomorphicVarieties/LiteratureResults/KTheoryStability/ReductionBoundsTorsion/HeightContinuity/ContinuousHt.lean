import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeightContinuity.MatrixTupleDistortionPos

open NumberField Matrix UpperTheory.V.KT
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.KB.HeightDistance

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

theorem emb_val (γ : Gm L N) (w : InfinitePlace L) :
    (((emb L N γ) w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      (γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) := by
  ext i j; rfl

theorem lm_comp (B : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ) (γ : Gm L N) :
    lm (fun w => B w * (γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w)) = lm B := by
  have key : ∀ y : Lat L N,
      tv (fun w => B w * (γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w)) y =
        tv B (((γ : Matrix (Fin N) (Fin N) (𝓞 L)) *ᵥ y : Fin N → 𝓞 L) : Lat L N) := by
    intro y
    unfold tv toR
    refine Finset.sum_congr rfl fun w _ => ?_
    congr 1
    rw [← Matrix.mulVec_mulVec]
    congr 1
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
  have hinv : ∀ y : Fin N → 𝓞 L, ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)) *ᵥ
      ((γ : Matrix (Fin N) (Fin N) (𝓞 L)) *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hinv' : ∀ y : Fin N → 𝓞 L, (γ : Matrix (Fin N) (Fin N) (𝓞 L)) *ᵥ
      (((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)) *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  let e0 : Lat L N ≃ Lat L N :=
    ⟨fun y => ((γ : Matrix (Fin N) (Fin N) (𝓞 L)) *ᵥ (y : Fin N → 𝓞 L) : Fin N → 𝓞 L),
     fun y => (((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)) *ᵥ (y : Fin N → 𝓞 L) : Fin N → 𝓞 L),
     fun y => hinv y, fun y => hinv' y⟩
  have h0 : ∀ y : Lat L N, y ≠ 0 ↔ e0 y ≠ 0 := by
    intro y
    refine not_congr ⟨fun h => ?_, fun h => ?_⟩
    · rw [h]
      show (γ : Matrix (Fin N) (Fin N) (𝓞 L)) *ᵥ (0 : Fin N → 𝓞 L) = 0
      exact Matrix.mulVec_zero _
    · rw [← e0.left_inv y]
      show ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)) *ᵥ (e0 y : Fin N → 𝓞 L) = 0
      rw [h]
      exact Matrix.mulVec_zero _
  let e : {y : Lat L N // y ≠ 0} ≃ {y : Lat L N // y ≠ 0} :=
    e0.subtypeEquiv (p := fun y => y ≠ 0) (q := fun y => y ≠ 0) h0
  unfold lm
  refine Equiv.iInf_congr e ?_
  intro y
  exact (key y.1).symm

theorem lm_iv_emb (γ : Gm L N) (x : Gp L N) : lm (iv (emb L N γ * x)) = lm (iv x) := by
  have h : iv (emb L N γ * x) =
      fun w => iv x w * ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) := by
    funext w
    rw [← emb_val]
    unfold iv
    simp only [Pi.mul_apply, map_inv]
    rw [_root_.mul_inv_rev, Units.val_mul, Pi.inv_apply]
  rw [h, lm_comp]

def gT (γ : Gm L N) : Gm L N :=
  ⟨(γ : Matrix (Fin N) (Fin N) (𝓞 L))ᵀ, ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L))ᵀ,
    by rw [← transpose_mul, Units.inv_mul, transpose_one],
    by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩

theorem lm_tp_emb (γ : Gm L N) (x : Gp L N) : lm (tp (emb L N γ * x)) = lm (tp x) := by
  have h : tp (emb L N γ * x) =
      fun w => tp x w * ((gT γ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) := by
    funext w
    unfold tp
    simp only [Pi.mul_apply, Units.val_mul, Matrix.transpose_mul, emb_val]
    rfl
  rw [h, lm_comp]

private theorem re_star_dotProduct_self_eq_nsq (v : Fin N → ℂ) : (star v ⬝ᵥ v).re = nsq v := by
  unfold nsq
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

private theorem actL_one_eq_hB_iv (x : Gp L N) : actL x (one L N) = hB (iv x) := by
  apply Subtype.ext
  funext w
  show (((x w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)ᴴ * 1 *
      (((x w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
    (((x w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)ᴴ *
      (((x w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
  rw [Matrix.mul_one]

private theorem lam_hB_eq_lm (B : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ) : lam (hB B) = lm B := by
  unfold lam lm
  refine iInf_congr fun y => ?_
  show qR (hB B) (toR y.1) = tv B y.1
  unfold qR tv
  refine Finset.sum_congr rfl fun w _ => ?_
  show (star (toR y.1 w) ⬝ᵥ ((B w)ᴴ * B w) *ᵥ toR y.1 w).re = nsq (B w *ᵥ toR y.1 w)
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, re_star_dotProduct_self_eq_nsq]

private theorem dualH_hB_iv_eq_hB_tp (x : Gp L N) : dualH (hB (iv x)) = hB (tp x) := by
  apply Subtype.ext
  funext w
  show (((((x w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)ᴴ *
      (((x w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ))⁻¹)ᵀ =
    ((x w : Matrix (Fin N) (Fin N) ℂ)ᵀ)ᴴ * (x w : Matrix (Fin N) (Fin N) ℂ)ᵀ
  have hinv : ((((x w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)ᴴ *
      (((x w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ))⁻¹ =
      (x w : Matrix (Fin N) (Fin N) ℂ) * (x w : Matrix (Fin N) (Fin N) ℂ)ᴴ := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (((x w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ),
      Units.inv_mul, Matrix.one_mul, ← Matrix.conjTranspose_mul, Units.mul_inv,
      Matrix.conjTranspose_one]
  rw [hinv, Matrix.transpose_mul]
  rfl

private theorem ht_eq_inv_lm_iv_mul_lm_tp (x : Gp L N) : ht x = (lm (iv x) * lm (tp x))⁻¹ := by
  unfold ht
  rw [actL_one_eq_hB_iv, dualH_hB_iv_eq_hB_tp, lam_hB_eq_lm, lam_hB_eq_lm]

theorem ht_emb (γ : Gm L N) (x : Gp L N) : ht (emb L N γ * x) = ht x := by
  rw [ht_eq, ht_eq, lm_iv_emb, lm_tp_emb]

theorem q_smul_hB (c : ℝ) (B : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ) (y : Lat L N) :
    q (c • hB B) y = c * tv B y := by
  show qR (c • hB B) (toR y) = c * tv B y
  unfold qR tv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  show (star (toR y w) ⬝ᵥ (c • ((B w)ᴴ * B w)) *ᵥ toR y w).re = c * nsq (B w *ᵥ toR y w)
  rw [Matrix.smul_mulVec, dotProduct_smul, Complex.smul_re, smul_eq_mul,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, re_star_dotProduct_self_eq_nsq]

theorem smul_mem_Ry (B : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ) (hpos : 0 < lm B) :
    (lm B)⁻¹ • hB B ∈ Ry L N := fun y hy => by
  rw [q_smul_hB, le_inv_mul_iff₀ hpos, mul_one]
  exact lm_le B ⟨y, hy⟩

theorem det_smul_hB (t : ℝ) (B : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ) (w : InfinitePlace L) :
    (mat (t • hB B) w).det.re = t ^ N * ‖(B w).det‖ ^ 2 := by
  show (t • ((B w)ᴴ * B w)).det.re = t ^ N * ‖(B w).det‖ ^ 2
  have hs : t • ((B w)ᴴ * B w) = (t : ℂ) • ((B w)ᴴ * B w) := by
    ext i j
    simp [Complex.real_smul]
  rw [hs, Matrix.det_smul, Fintype.card_fin, Matrix.det_mul, Matrix.det_conjTranspose,
    Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.ofReal_re]

theorem lm_prod_le [IsTotallyComplex L] (hN : 1 ≤ N) (x : Gp L N) :
    lm (iv x) * lm (tp x) ≤ max 1 ((I0 L N : ℝ) ^ 2) := by
  have ha := lm_iv_pos hN x
  have hb := lm_tp_pos hN x
  have h1 := detlow L N _ (smul_mem_Ry (iv x) ha)
  have h2 := detlow L N _ (smul_mem_Ry (tp x) hb)
  simp only [det_smul_hB, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    ← pow_mul] at h1 h2
  have hP : (∏ w, ‖(iv x w).det‖ ^ 2) * ∏ w, ‖(tp x w).det‖ ^ 2 = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun w _ => ?_
    show ‖(((x w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).det‖ ^ 2 *
      ‖((x w : Matrix (Fin N) (Fin N) ℂ)ᵀ).det‖ ^ 2 = 1
    rw [Matrix.det_transpose, ← mul_pow, ← norm_mul, ← Matrix.det_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.det_one, norm_one, one_pow]
  have hr : 0 < Fintype.card (InfinitePlace L) := Fintype.card_pos
  have hk0 : N * Fintype.card (InfinitePlace L) ≠ 0 := Nat.mul_ne_zero (by omega) hr.ne'
  generalize N * Fintype.card (InfinitePlace L) = k at h1 h2 hk0
  have hprod := one_le_mul_of_one_le_of_one_le h1 h2
  have key : 1 ≤ (I0 L N : ℝ) ^ 2 * ((lm (iv x) * lm (tp x)) ^ k)⁻¹ := by
    refine le_of_le_of_eq hprod ?_
    rw [mul_pow, mul_inv, ← inv_pow, ← inv_pow]
    linear_combination ((I0 L N : ℝ) ^ 2 * (lm (iv x))⁻¹ ^ k * (lm (tp x))⁻¹ ^ k) * hP
  rw [le_mul_inv_iff₀ (by positivity), one_mul] at key
  rcases le_or_gt (lm (iv x) * lm (tp x)) 1 with hab | hab
  · exact le_max_of_le_left hab
  · exact le_max_of_le_right ((le_self_pow₀ hab.le hk0).trans key)

theorem ht_lower [IsTotallyComplex L] (hN : 1 ≤ N) :
    ∃ c, 0 < c ∧ ∀ x : Gp L N, c ≤ ht x := by
  refine ⟨(max 1 ((I0 L N : ℝ) ^ 2))⁻¹, by positivity, fun x => ?_⟩
  have ha := lm_iv_pos hN x
  have hb := lm_tp_pos hN x
  rw [ht_eq_inv_lm_iv_mul_lm_tp]
  exact inv_anti₀ (mul_pos ha hb) (lm_prod_le hN x)

theorem ht_mul_le [IsTotallyComplex L] (hN : 1 ≤ N) (x g : Gp L N) :
    ht (x * g) ≤ (dist1 (fun w => ((g w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) *
      dist1 (tp g⁻¹)) * ht x := by
  have h1 := lm_iv_le hN x g
  have h2 := lm_tp_le hN x g
  have ha := lm_iv_pos hN x
  have hb := lm_tp_pos hN x
  have ha' := lm_iv_pos hN (x * g)
  have hb' := lm_tp_pos hN (x * g)
  have hD1 := matrixTupleDistortion_pos (fun w => ((g w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ))
  have hD2 := matrixTupleDistortion_pos (tp g⁻¹)
  rw [ht_eq, ht_eq, ← div_eq_mul_inv, le_div_iff₀ (mul_pos ha hb), inv_mul_le_iff₀ (mul_pos ha' hb')]
  calc lm (iv x) * lm (tp x)
      ≤ (dist1 (fun w => ((g w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) * lm (iv (x * g))) *
        (dist1 (tp g⁻¹) * lm (tp (x * g))) :=
        mul_le_mul h1 h2 hb.le (by positivity)
    _ = _ := by ring

theorem ht_pos [IsTotallyComplex L] (hN : 1 ≤ N) (x : Gp L N) : 0 < ht x := by
  rw [ht_eq_inv_lm_iv_mul_lm_tp]
  exact inv_pos.mpr (mul_pos (lm_iv_pos hN x) (lm_tp_pos hN x))

private theorem continuous_dist1_mul_dist1_tp_inv :
    Continuous (fun g : Gp L N => dist1 (fun w => ((g w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) *
      dist1 (tp g⁻¹)) := by
  unfold dist1 tp
  simp only [Matrix.transpose_apply, Pi.inv_apply]
  fun_prop

private theorem dist1_one_mul_dist1_tp_one_eq_one :
    dist1 (fun w => (((1 : Gp L N) w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) *
      dist1 (tp (1 : Gp L N)⁻¹) = 1 := by
  have h : tp (1 : Gp L N)⁻¹ = fun _ => 1 := by
    funext w
    show ((((1 : Gp L N)⁻¹ w : GL (Fin N) ℂ)) : Matrix (Fin N) (Fin N) ℂ)ᵀ = 1
    rw [inv_one]
    show ((1 : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)ᵀ = 1
    rw [Units.val_one, Matrix.transpose_one]
  rw [h]
  simp [dist1]

private theorem dist1_pos {ι : Type} [Fintype ι] (f : ι → Matrix (Fin N) (Fin N) ℂ) :
    0 < dist1 f := by
  unfold dist1
  positivity

theorem continuous_ht [IsTotallyComplex L] (hN : 1 ≤ N) : Continuous (ht : Gp L N → ℝ) := by
  have hEc := continuous_dist1_mul_dist1_tp_inv (L := L) (N := N)
  rw [continuous_iff_continuousAt]
  intro x
  have hg : Continuous fun y : Gp L N => x⁻¹ * y := continuous_const.mul continuous_id
  have hgi : Continuous fun y : Gp L N => (x⁻¹ * y)⁻¹ := hg.inv
  have hup : Filter.Tendsto
      (fun y : Gp L N => (dist1 (fun w => (((x⁻¹ * y) w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) *
        dist1 (tp (x⁻¹ * y)⁻¹)) * ht x) (nhds x) (nhds (ht x)) := by
    have h := ((hEc.comp hg).tendsto x).mul_const (ht x)
    simp only [Function.comp_def, inv_mul_cancel, dist1_one_mul_dist1_tp_one_eq_one, one_mul] at h
    exact h
  have hlo : Filter.Tendsto
      (fun y : Gp L N => ht x / (dist1 (fun w => (((x⁻¹ * y)⁻¹ w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) *
        dist1 (tp (x⁻¹ * y)⁻¹⁻¹))) (nhds x) (nhds (ht x)) := by
    have h := (hEc.comp hgi).tendsto x
    have hv : ((fun g : Gp L N => dist1 (fun w => ((g w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) *
        dist1 (tp g⁻¹)) ∘ (fun y : Gp L N => (x⁻¹ * y)⁻¹)) x = 1 := by
      show dist1 (fun w => ((((x⁻¹ * x)⁻¹) w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) *
        dist1 (tp (x⁻¹ * x)⁻¹⁻¹) = 1
      rw [inv_mul_cancel, inv_one]
      exact dist1_one_mul_dist1_tp_one_eq_one
    rw [hv] at h
    have h2 := (tendsto_const_nhds (x := ht x) (f := nhds x)).div h one_ne_zero
    rw [div_one] at h2
    exact h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hup (fun y => ?_) (fun y => ?_)
  · have h := ht_mul_le hN y (x⁻¹ * y)⁻¹
    rw [_root_.mul_inv_rev, inv_inv, mul_inv_cancel_left] at h
    rw [div_le_iff₀ (mul_pos (dist1_pos _) (dist1_pos _)), mul_comm]
    simpa only [_root_.mul_inv_rev, inv_inv] using h
  · have h := ht_mul_le hN x (x⁻¹ * y)
    rw [mul_inv_cancel_left] at h
    exact h

theorem ht_compact [IsTotallyComplex L] (hN : 1 ≤ N) (K : Set (Gp L N)) (hK : IsCompact K) :
    ∃ C, ∀ g ∈ K, ∀ x, ht (x * g) ≤ C * ht x := by
  obtain ⟨C, hC⟩ := hK.bddAbove_image (continuous_dist1_mul_dist1_tp_inv (L := L) (N := N)).continuousOn
  refine ⟨C, fun g hg x => ?_⟩
  have hEg := hC ⟨g, hg, rfl⟩
  exact (ht_mul_le hN x g).trans (mul_le_mul_of_nonneg_right hEg (ht_pos hN x).le)

end PositivityTheory.KB.HeightDistance
