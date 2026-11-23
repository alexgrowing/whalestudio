import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Smoothing
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.DotVecMulVec

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

open TraceLipschitz

section GTLipPf

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

private theorem rho_nonneg' (x : ℝ) : 0 ≤ rho x := by
  unfold rho; exact Real.smoothTransition.nonneg _

private theorem rho_le_one' (x : ℝ) : rho x ≤ 1 := by
  unfold rho; exact Real.smoothTransition.le_one _

private theorem exists_lipschitz_const_rho : ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : ℝ, |rho x - rho y| ≤ K * |x - y| := by
  obtain ⟨K, hK⟩ := (Real.smoothTransition.contDiff (n := 1)).contDiffOn.exists_lipschitzOnWith
    (s := Set.Icc (0 : ℝ) 1) one_ne_zero (convex_Icc 0 1) isCompact_Icc
  have hc : ∀ x : ℝ, Real.smoothTransition x = Real.smoothTransition (max 0 (min 1 x)) := by
    intro x
    rcases le_total x 0 with hx | hx
    · rw [Real.smoothTransition.zero_of_nonpos hx, Real.smoothTransition.zero_of_nonpos]
      exact max_le le_rfl (min_le_of_right_le hx)
    · rcases le_total x 1 with hx1 | hx1
      · rw [min_eq_right hx1, max_eq_right hx]
      · rw [Real.smoothTransition.one_of_one_le hx1, Real.smoothTransition.one_of_one_le]
        rw [min_eq_left hx1, max_eq_right zero_le_one]
  have hcl : ∀ x y : ℝ, |max 0 (min 1 x) - max 0 (min 1 y)| ≤ |x - y| := by
    intro x y
    have h1 := abs_max_sub_max_le_abs (min 1 x) (min 1 y) (0 : ℝ)
    rw [max_comm (min 1 x), max_comm (min 1 y)] at h1
    have h2 := abs_min_sub_min_le_max (1 : ℝ) x 1 y
    rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)] at h2
    exact h1.trans h2
  refine ⟨K / 3, by positivity, fun x y => ?_⟩
  unfold rho
  rw [hc, hc ((4 - y) / 3)]
  have hm : ∀ t : ℝ, max 0 (min 1 t) ∈ Set.Icc (0 : ℝ) 1 := fun t =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have := hK.dist_le_mul _ (hm ((4 - x) / 3)) _ (hm ((4 - y) / 3))
  rw [Real.dist_eq, Real.dist_eq] at this
  calc _ ≤ (K : ℝ) * |max 0 (min 1 ((4 - x) / 3)) - max 0 (min 1 ((4 - y) / 3))| := this
    _ ≤ K * |(4 - x) / 3 - (4 - y) / 3| := mul_le_mul_of_nonneg_left (hcl _ _) K.2
    _ = K / 3 * |x - y| := by
      rw [show (4 - x) / 3 - (4 - y) / 3 = -(x - y) / 3 by ring, abs_div, abs_neg]
      norm_num
      ring

private theorem norm_inner_sq_le_of_posSemidef {n : Type} [Fintype n] (M : Matrix n n ℂ) (hM : M.PosSemidef)
    (u v : n → ℂ) :
    ‖star u ⬝ᵥ M *ᵥ v‖ ^ 2 ≤ (star u ⬝ᵥ M *ᵥ u).re * (star v ⬝ᵥ M *ᵥ v).re := by
  letI := M.toSeminormedAddCommGroup hM
  letI := M.toInnerProductSpace hM
  have h1 := inner_mul_inner_self_le (𝕜 := ℂ) u v
  have e : ∀ x y : n → ℂ, (inner ℂ x y : ℂ) = star x ⬝ᵥ M *ᵥ y := fun x y => by
    show (M *ᵥ y) ⬝ᵥ star x = _
    exact dotProduct_comm _ _
  have e4 : ‖(inner ℂ v u : ℂ)‖ = ‖(inner ℂ u v : ℂ)‖ := norm_inner_symm _ _
  rw [e4, e u v, e u u, e v v] at h1
  simpa [sq] using h1

private theorem qR_smul_left (h : HS L N) (z : VR L N) (c : ℝ) : qR (c • h) z = c * qR h z := by
  simp [qR, mat_smul, Matrix.smul_mulVec, dotProduct_smul, Finset.mul_sum]

private theorem qR_add_left (h k : HS L N) (z : VR L N) : qR (h + k) z = qR h z + qR k z := by
  simp [qR, mat_add, Matrix.add_mulVec, dotProduct_add, Finset.sum_add_distrib]

private theorem qR_zero_left (z : VR L N) : qR (0 : HS L N) z = 0 := by
  simp [qR, mat_zero]

private theorem qR_finset_sum_left {ι : Type} (S : Finset ι) (f : ι → HS L N) (z : VR L N) :
    qR (∑ i ∈ S, f i) z = ∑ i ∈ S, qR (f i) z := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [qR_zero_left]
  | insert a S ha ih => rw [Finset.sum_insert ha, qR_add_left, ih, Finset.sum_insert ha]

private theorem qR_rk_eq_sum_norm_sq_inner (p : HS L N) (v : UpperTheory.V.KT.Lat L N) (z : VR L N) :
    qR (rk p v) z = ∑ w, ‖star (z w) ⬝ᵥ mat p w *ᵥ toR v w‖ ^ 2 := by
  unfold qR
  refine Finset.sum_congr rfl fun w _ => ?_
  have : mat (rk p v) w = vecMulVec (mat p w *ᵥ toR v w) (star (mat p w *ᵥ toR v w)) := rfl
  rw [this, Matrix.vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, smul_eq_mul]
  have hd : star (mat p w *ᵥ toR v w) ⬝ᵥ z w =
      (starRingEnd ℂ) (star (z w) ⬝ᵥ mat p w *ᵥ toR v w) := by
    rw [starRingEnd_apply, Matrix.star_dotProduct]
  rw [hd, Complex.conj_mul']
  norm_cast

private theorem qR_term_eq_normalized_weighted_sum (s : ℝ) (p : HS L N) (z : VR L N) (S : Finset (UpperTheory.V.KT.Lat L N))
    (hS : ∀ v, v ∉ S → rho (q p v / s) = 0) :
    qR (term s p) z = (s ^ 2 * ∑ v ∈ S, rho (q p v / s))⁻¹ *
      ∑ v ∈ S, rho (q p v / s) * ∑ w, ‖star (z w) ⬝ᵥ mat p w *ᵥ toR v w‖ ^ 2 := by
  have h1 : zed s p = ∑ v ∈ S, rho (q p v / s) := by
    show (∑ᶠ v, rho (q p v / s)) = _
    apply finsum_eq_sum_of_support_subset
    intro v hv
    by_contra hvS
    exact hv (hS v hvS)
  have h2 : (∑ᶠ v, rho (q p v / s) • rk p v) = ∑ v ∈ S, rho (q p v / s) • rk p v := by
    apply finsum_eq_sum_of_support_subset
    intro v hv
    by_contra hvS
    exact hv (by simp [hS v hvS])
  have h3 : term s p = (s ^ 2 * zed s p)⁻¹ • ∑ᶠ v, rho (q p v / s) • rk p v := rfl
  rw [h3, h2, h1, qR_smul_left, qR_finset_sum_left]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [qR_smul_left, qR_rk_eq_sum_norm_sq_inner]

private theorem qR_nonneg_VR_of_mem_Pos (p : HS L N) (hp : p ∈ Pos L N) (y : VR L N) : 0 ≤ qR p y := by
  have hp' : ∀ w, (mat p w).PosDef := hp
  exact Finset.sum_nonneg fun w _ => (hp' w).posSemidef.re_dotProduct_nonneg (y w)

private theorem sum_norm_sq_inner_mat_toR_le_qR_mul_q (p : HS L N) (hp : p ∈ Pos L N) (z : VR L N)
    (v : UpperTheory.V.KT.Lat L N) :
    ∑ w, ‖star (z w) ⬝ᵥ mat p w *ᵥ toR v w‖ ^ 2 ≤ qR p z * q p v := by
  have hp' : ∀ w, (mat p w).PosDef := hp
  have hX : ∀ w, 0 ≤ (star (z w) ⬝ᵥ mat p w *ᵥ z w).re := fun w =>
    (hp' w).posSemidef.re_dotProduct_nonneg (z w)
  have hY : ∀ w, 0 ≤ (star (toR v w) ⬝ᵥ mat p w *ᵥ toR v w).re := fun w =>
    (hp' w).posSemidef.re_dotProduct_nonneg (toR v w)
  show _ ≤ (∑ w, (star (z w) ⬝ᵥ mat p w *ᵥ z w).re) *
    ∑ w, (star (toR v w) ⬝ᵥ mat p w *ᵥ toR v w).re
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun w _ => ?_
  refine (norm_inner_sq_le_of_posSemidef _ (hp' w).posSemidef _ _).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (f := fun w => (star (toR v w) ⬝ᵥ mat p w *ᵥ toR v w).re)
      (fun w _ => hY w) (Finset.mem_univ w)) (hX w)

private theorem place_form_perturbation_bound_of_sq_le (h k : HS L N) (hp : h ∈ Pos L N) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 4)
    (h5 : ∀ (w : InfinitePlace L) (u v : Fin N → ℂ),
      ‖star u ⬝ᵥ mat k w *ᵥ v - star u ⬝ᵥ mat h w *ᵥ v‖ ^ 2 ≤
        4 * δ ^ 2 * (star u ⬝ᵥ mat h w *ᵥ u).re * (star v ⬝ᵥ mat h w *ᵥ v).re)
    (z : VR L N) (v : UpperTheory.V.KT.Lat L N) :
    |∑ w, ‖star (z w) ⬝ᵥ mat k w *ᵥ toR v w‖ ^ 2 - ∑ w, ‖star (z w) ⬝ᵥ mat h w *ᵥ toR v w‖ ^ 2|
      ≤ 5 * δ * (qR h z * q h v) := by
  have hp' : ∀ w, (mat h w).PosDef := hp
  have hX : ∀ w, 0 ≤ (star (z w) ⬝ᵥ mat h w *ᵥ z w).re := fun w =>
    (hp' w).posSemidef.re_dotProduct_nonneg (z w)
  have hY : ∀ w, 0 ≤ (star (toR v w) ⬝ᵥ mat h w *ᵥ toR v w).re := fun w =>
    (hp' w).posSemidef.re_dotProduct_nonneg (toR v w)
  have hw : ∀ w, |‖star (z w) ⬝ᵥ mat k w *ᵥ toR v w‖ ^ 2 - ‖star (z w) ⬝ᵥ mat h w *ᵥ toR v w‖ ^ 2|
      ≤ 5 * δ * ((star (z w) ⬝ᵥ mat h w *ᵥ z w).re *
        (star (toR v w) ⬝ᵥ mat h w *ᵥ toR v w).re) := by
    intro w
    set xk := star (z w) ⬝ᵥ mat k w *ᵥ toR v w
    set xh := star (z w) ⬝ᵥ mat h w *ᵥ toR v w
    set P := (star (z w) ⬝ᵥ mat h w *ᵥ z w).re * (star (toR v w) ⬝ᵥ mat h w *ᵥ toR v w).re
    have hP : 0 ≤ P := mul_nonneg (hX w) (hY w)
    have hA : ‖xh‖ ^ 2 ≤ P := norm_inner_sq_le_of_posSemidef _ (hp' w).posSemidef _ _
    have hB : ‖xk - xh‖ ^ 2 ≤ 4 * δ ^ 2 * P := by
      have := h5 w (z w) (toR v w)
      simp only [P]
      linarith
    have hEA : |‖xk‖ - ‖xh‖| ≤ ‖xk - xh‖ := abs_norm_sub_norm_le xk xh
    have hA0 := norm_nonneg xh
    have hB0 := norm_nonneg (xk - xh)
    have hE0 := norm_nonneg xk
    have hAB : 2 * ‖xh‖ * ‖xk - xh‖ ≤ 4 * δ * P := by
      have h1 : (2 * ‖xh‖ * ‖xk - xh‖) ^ 2 ≤ (4 * δ * P) ^ 2 := by
        have : (2 * ‖xh‖ * ‖xk - xh‖) ^ 2 = 4 * (‖xh‖ ^ 2 * ‖xk - xh‖ ^ 2) := by ring
        rw [this]
        have := mul_le_mul hA hB (by positivity) hP
        nlinarith
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h1
    have hBB : ‖xk - xh‖ ^ 2 ≤ δ * P := by
      have h4 : 4 * δ ^ 2 ≤ δ := by nlinarith
      have := mul_le_mul_of_nonneg_right h4 hP
      linarith
    have hE : ‖xk‖ ≤ ‖xh‖ + ‖xk - xh‖ := by
      have := (abs_le.1 hEA).2
      linarith
    rw [abs_le]
    constructor
    · have : ‖xh‖ - ‖xk - xh‖ ≤ ‖xk‖ := by
        have := (abs_le.1 hEA).1
        linarith
      nlinarith
    · nlinarith
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun w _ => hw w).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  show _ ≤ (∑ w, (star (z w) ⬝ᵥ mat h w *ᵥ z w).re) *
    ∑ w, (star (toR v w) ⬝ᵥ mat h w *ᵥ toR v w).re
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun w _ => ?_
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (f := fun w => (star (toR v w) ⬝ᵥ mat h w *ᵥ toR v w).re)
      (fun w _ => hY w) (Finset.mem_univ w)) (hX w)

private theorem rk_zero_right_of_hs (p : HS L N) : rk p 0 = 0 := by
  have h0 : toR (0 : UpperTheory.V.KT.Lat L N) = 0 := by
    funext w a
    simp [toR]
  apply Subtype.ext
  funext w
  have : mat (rk p 0) w = mat 0 w := by
    show vecMulVec (mat p w *ᵥ toR 0 w) (star (mat p w *ᵥ toR 0 w)) = _
    simp [h0, mat_zero]
  unfold mat at this
  exact this

private theorem abs_ratio_perturbation_bound_of_estimates (s Zh FinalFormK Ah Ak Q δ M C1 K : ℝ) (hs : 0 < s) (hZh : 0 < Zh)
    (hZk : 0 < FinalFormK) (hAh0 : 0 ≤ Ah) (hAh : Ah ≤ 4 * s * Q * Zh)
    (hA : |Ak - Ah| ≤ (128 * K + 40) * δ * s * Q * M) (hZ : |FinalFormK - Zh| ≤ 8 * K * δ * M)
    (hM : M ≤ C1 * FinalFormK) (hδ : 0 ≤ δ) (hQ : 0 ≤ Q) (hK : 0 ≤ K) (hM0 : 0 ≤ M) :
    |(s ^ 2 * FinalFormK)⁻¹ * Ak - (s ^ 2 * Zh)⁻¹ * Ah| ≤ (160 * K + 40) * C1 * δ / s * Q := by
  have e : (s ^ 2 * FinalFormK)⁻¹ * Ak - (s ^ 2 * Zh)⁻¹ * Ah =
      ((Ak - Ah) * Zh + Ah * (Zh - FinalFormK)) / (s ^ 2 * FinalFormK * Zh) := by
    field_simp
    ring
  have hden : (0 : ℝ) < s ^ 2 * FinalFormK * Zh := by positivity
  rw [e, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have hZ' : |Zh - FinalFormK| ≤ 8 * K * δ * M := by rwa [abs_sub_comm]
  calc |(Ak - Ah) * Zh + Ah * (Zh - FinalFormK)|
      ≤ |Ak - Ah| * Zh + Ah * |Zh - FinalFormK| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_pos hZh, abs_of_nonneg hAh0]
    _ ≤ (128 * K + 40) * δ * s * Q * M * Zh + (4 * s * Q * Zh) * (8 * K * δ * M) := by
        gcongr
    _ = (160 * K + 40) * δ * s * Q * Zh * M := by ring
    _ ≤ (160 * K + 40) * δ * s * Q * Zh * (C1 * FinalFormK) := by gcongr
    _ = (160 * K + 40) * C1 * δ / s * Q * (s ^ 2 * FinalFormK * Zh) := by
        field_simp

set_option maxHeartbeats 1600000 in
theorem pf_GTLip : GTLip := by
  unfold GTLip Basic Count TLip
  intro hB hC L _ _ N hN
  obtain ⟨K, hK0, hK⟩ := exists_lipschitz_const_rho
  obtain ⟨C1, hC1pos, hC1⟩ := hC L N 10
  refine ⟨(160 * K + 40) * C1, fun s hs h hh z => ?_⟩
  obtain ⟨hP, -, -, hCl, h5, -⟩ := hB L N hN
  obtain ⟨-, hlam, -, -, hfin⟩ := hP h hh
  have hQ : 0 ≤ qR h z := qR_nonneg_VR_of_mem_Pos h hh z
  have hr1 : ∀ x : ℝ, x ≤ 1 → rho x = 1 := fun x hx => by
    unfold rho
    exact Real.smoothTransition.one_of_one_le (by linarith)
  have hr0 : ∀ x : ℝ, 4 ≤ x → rho x = 0 := fun x hx => by
    unfold rho
    exact Real.smoothTransition.zero_of_nonpos (by linarith)
  have hrn : ∀ x, 0 ≤ rho x := rho_nonneg'
  have hrl : ∀ x, rho x ≤ 1 := rho_le_one'
  have hq0 : q h 0 = 0 := by
    have h0 : toR (0 : UpperTheory.V.KT.Lat L N) = 0 := by
      funext w a
      simp [toR]
    show qR h (toR 0) = 0
    rw [h0]
    simp [qR]
  set S := (hfin (8 * s)).toFinset with hSdef
  have hmemS : ∀ v, v ∈ S ↔ q h v ≤ 8 * s := fun v => by simp [S]
  set T := (hfin (4 / 5 * s)).toFinset with hTdef
  have hmemT : ∀ v, v ∈ T ↔ q h v ≤ 4 / 5 * s := fun v => by simp [T]
  have hTS : T ⊆ S := fun v hv => by
    rw [hmemS]
    rw [hmemT] at hv
    linarith
  have hTcard : (1 : ℝ) ≤ T.card := by
    have : 0 < T.card := Finset.card_pos.2 ⟨0, by rw [hmemT, hq0]; positivity⟩
    exact_mod_cast this
  have hSh : ∀ v, v ∉ S → rho (q h v / s) = 0 := fun v hv => by
    rw [hmemS, not_le] at hv
    exact hr0 _ (by rw [le_div_iff₀ hs]; linarith)
  set ah : UpperTheory.V.KT.Lat L N → ℝ := fun v => ∑ w, ‖star (z w) ⬝ᵥ mat h w *ᵥ toR v w‖ ^ 2
    with hah
  have hah0 : ∀ v, 0 ≤ ah v := fun v => Finset.sum_nonneg fun w _ => by positivity
  have hahle : ∀ v, ah v ≤ qR h z * q h v := fun v => sum_norm_sq_inner_mat_toR_le_qR_mul_q h hh z v
  have hZh : (T.card : ℝ) ≤ ∑ v ∈ S, rho (q h v / s) := by
    have e1 : ∀ v ∈ T, rho (q h v / s) = 1 := fun v hv => by
      rw [hmemT] at hv
      exact hr1 _ (by rw [div_le_one hs]; linarith)
    calc (T.card : ℝ) = ∑ v ∈ T, rho (q h v / s) := by
          rw [Finset.sum_congr rfl e1]
          simp
      _ ≤ ∑ v ∈ S, rho (q h v / s) := Finset.sum_le_sum_of_subset_of_nonneg hTS fun _ _ _ => hrn _
  have hZhpos : 0 < ∑ v ∈ S, rho (q h v / s) := by linarith
  have hAh0 : 0 ≤ ∑ v ∈ S, rho (q h v / s) * ah v :=
    Finset.sum_nonneg fun v _ => mul_nonneg (hrn _) (hah0 v)
  have hAh : ∑ v ∈ S, rho (q h v / s) * ah v ≤ 4 * s * qR h z * ∑ v ∈ S, rho (q h v / s) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    by_cases hv : q h v ≤ 4 * s
    · have h1 := hahle v
      have h2 : qR h z * q h v ≤ qR h z * (4 * s) := mul_le_mul_of_nonneg_left hv hQ
      have h3 := hrn (q h v / s)
      nlinarith
    · rw [hr0 _ (by rw [le_div_iff₀ hs]; linarith)]
      simp
  have hTh := qR_term_eq_normalized_weighted_sum s h z S hSh
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hTh]
    exact mul_nonneg (inv_nonneg.2 (by positivity)) hAh0
  · rw [hTh, inv_mul_le_iff₀ (by positivity)]
    calc _ ≤ 4 * s * qR h z * ∑ v ∈ S, rho (q h v / s) := hAh
      _ = s ^ 2 * (∑ v ∈ S, rho (q h v / s)) * (4 / s * qR h z) := by
        field_simp
  · intro hl
    show (s ^ 2 * zed s h)⁻¹ • ∑ᶠ v, rho (q h v / s) • rk h v = 0
    have e : ∀ v, rho (q h v / s) • rk h v = 0 := by
      intro v
      by_cases hv : v = 0
      · rw [hv, rk_zero_right_of_hs, smul_zero]
      · rw [hr0 _ (by rw [le_div_iff₀ hs]; linarith [hlam v hv]), zero_smul]
    simp only [e, finsum_zero, smul_zero]
  · intro δ hδ0 hδ k hk
    have hkP : k ∈ Pos L N := (hCl δ hδ0 (by linarith) h hh k hk).1
    have h5' := h5 δ hδ0 h hh k hk
    have hClz : ∀ y, |qR k y - qR h y| ≤ δ * qR h y := hk
    have hqk : ∀ v, (1 - δ) * q h v ≤ q k v ∧ q k v ≤ (1 + δ) * q h v := fun v => by
      have := abs_le.1 (hClz (toR v))
      constructor
      · show (1 - δ) * qR h (toR v) ≤ qR k (toR v)
        linarith
      · show qR k (toR v) ≤ (1 + δ) * qR h (toR v)
        linarith
    have hqh0 : ∀ v, 0 ≤ q h v := fun v => qR_nonneg_VR_of_mem_Pos h hh _
    have hSk : ∀ v, v ∉ S → rho (q k v / s) = 0 := fun v hv => by
      rw [hmemS, not_le] at hv
      have := (hqk v).1
      exact hr0 _ (by rw [le_div_iff₀ hs]; nlinarith)
    set ak : UpperTheory.V.KT.Lat L N → ℝ := fun v => ∑ w, ‖star (z w) ⬝ᵥ mat k w *ᵥ toR v w‖ ^ 2
      with hak
    have hak0 : ∀ v, 0 ≤ ak v := fun v => Finset.sum_nonneg fun w _ => by positivity
    have hTk := qR_term_eq_normalized_weighted_sum s k z S hSk
    have hZk : (T.card : ℝ) ≤ ∑ v ∈ S, rho (q k v / s) := by
      have e1 : ∀ v ∈ T, rho (q k v / s) = 1 := fun v hv => by
        rw [hmemT] at hv
        have := (hqk v).2
        have := hqh0 v
        exact hr1 _ (by rw [div_le_one hs]; nlinarith)
      calc (T.card : ℝ) = ∑ v ∈ T, rho (q k v / s) := by
            rw [Finset.sum_congr rfl e1]
            simp
        _ ≤ ∑ v ∈ S, rho (q k v / s) := Finset.sum_le_sum_of_subset_of_nonneg hTS fun _ _ _ => hrn _
    have hZkpos : 0 < ∑ v ∈ S, rho (q k v / s) := by linarith
    have hM : (S.card : ℝ) ≤ C1 * ∑ v ∈ S, rho (q k v / s) := by
      have := hC1 h hh (4 / 5 * s) (by positivity)
      rw [show (10 : ℝ) * (4 / 5 * s) = 8 * s by ring] at this
      rw [Set.ncard_eq_toFinset_card _ (hfin _), Set.ncard_eq_toFinset_card _ (hfin _)] at this
      calc (S.card : ℝ) ≤ C1 * T.card := this
        _ ≤ C1 * ∑ v ∈ S, rho (q k v / s) := mul_le_mul_of_nonneg_left hZk hC1pos.le
    have hρd : ∀ v ∈ S, |rho (q k v / s) - rho (q h v / s)| ≤ 8 * K * δ := fun v hv => by
      rw [hmemS] at hv
      have h1 := hK (q k v / s) (q h v / s)
      have h2 : |q k v / s - q h v / s| ≤ 8 * δ := by
        rw [← sub_div, abs_div, abs_of_pos hs, div_le_iff₀ hs]
        have := hClz (toR v)
        calc |q k v - q h v| ≤ δ * q h v := this
          _ ≤ δ * (8 * s) := mul_le_mul_of_nonneg_left hv hδ0
          _ = 8 * δ * s := by ring
      calc _ ≤ K * |q k v / s - q h v / s| := h1
        _ ≤ K * (8 * δ) := mul_le_mul_of_nonneg_left h2 hK0
        _ = 8 * K * δ := by ring
    have hZ : |∑ v ∈ S, rho (q k v / s) - ∑ v ∈ S, rho (q h v / s)| ≤ 8 * K * δ * S.card := by
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum hρd).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      ring_nf
      rfl
    have hA : |∑ v ∈ S, rho (q k v / s) * ak v - ∑ v ∈ S, rho (q h v / s) * ah v| ≤
        (128 * K + 40) * δ * s * qR h z * S.card := by
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hv' : ∀ v ∈ S, |rho (q k v / s) * ak v - rho (q h v / s) * ah v| ≤
          (128 * K + 40) * δ * s * qR h z := fun v hv => by
        have hvS := (hmemS v).1 hv
        have hd := hρd v hv
        have hakle : ak v ≤ 16 * s * qR h z := by
          have h1 := sum_norm_sq_inner_mat_toR_le_qR_mul_q k hkP z v
          have h2 := (hqk v).2
          have h3 : qR k z ≤ (1 + δ) * qR h z := by
            have := abs_le.1 (hClz z)
            linarith
          have h4 := qR_nonneg_VR_of_mem_Pos k hkP z
          have h5 := hqh0 v
          have h6 : q k v ≤ (1 + δ) * (8 * s) := h2.trans (mul_le_mul_of_nonneg_left hvS (by linarith))
          have h7 : 0 ≤ q k v := qR_nonneg_VR_of_mem_Pos k hkP _
          calc ak v ≤ qR k z * q k v := h1
            _ ≤ ((1 + δ) * qR h z) * ((1 + δ) * (8 * s)) := mul_le_mul h3 h6 h7 (by positivity)
            _ = ((1 + δ) * (1 + δ)) * (8 * s * qR h z) := by ring
            _ ≤ 2 * (8 * s * qR h z) := by
              have hd2 : (1 + δ) * (1 + δ) ≤ 2 := by nlinarith
              exact mul_le_mul_of_nonneg_right hd2 (by positivity)
            _ = 16 * s * qR h z := by ring
        have hdiff := place_form_perturbation_bound_of_sq_le h k hh δ hδ0 hδ h5' z v
        have hdiff' : |ak v - ah v| ≤ 40 * δ * s * qR h z := by
          refine hdiff.trans ?_
          have h1 := mul_le_mul_of_nonneg_left hvS hQ
          have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 5 * δ)
          linarith
        have e : rho (q k v / s) * ak v - rho (q h v / s) * ah v =
            (rho (q k v / s) - rho (q h v / s)) * ak v + rho (q h v / s) * (ak v - ah v) := by ring
        rw [e]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg (hak0 v), abs_of_nonneg (hrn _)]
        have t1 : |rho (q k v / s) - rho (q h v / s)| * ak v ≤ 8 * K * δ * (16 * s * qR h z) :=
          mul_le_mul hd hakle (hak0 v) (by positivity)
        have t2 : rho (q h v / s) * |ak v - ah v| ≤ 1 * (40 * δ * s * qR h z) :=
          mul_le_mul (hrl _) hdiff' (abs_nonneg _) zero_le_one
        linarith
      refine (Finset.sum_le_sum hv').trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      ring_nf
      rfl
    rw [hTk, hTh]
    exact abs_ratio_perturbation_bound_of_estimates s _ _ _ _ (qR h z) δ S.card C1 K hs hZhpos hZkpos hAh0 hAh hA hZ hM hδ0
      hQ hK0 (Nat.cast_nonneg _)

end GTLipPf

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
