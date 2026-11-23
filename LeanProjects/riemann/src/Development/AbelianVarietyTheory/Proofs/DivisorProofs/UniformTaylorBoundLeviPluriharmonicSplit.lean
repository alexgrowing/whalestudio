import Mathlib
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax

open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

namespace GlobalTheory.PluriTaylor

open Complex Set

variable {n : ℕ}

theorem smul_decomp (c : ℂ) (v : V n) : c • v = c.re • v + c.im • (I • v) := by
  ext j
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Complex.real_smul]
  conv_lhs => rw [← Complex.re_add_im c]
  ring

theorem vec_expand' (w : V n) : w = ∑ j, w j • bas n j := by
  have h := (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr w
  simpa [bas] using h.symm

theorem sum_re_im_eq (w : V n) :
    (∑ k, ((w k).re • bas n k + (w k).im • (I • bas n k))) = w := by
  rw [Finset.sum_congr rfl fun k _ => (smul_decomp (w k) (bas n k)).symm]
  exact (vec_expand' w).symm

theorem sum_I_eq (w : V n) :
    (∑ k, ((w k).re • (I • bas n k) - (w k).im • bas n k)) = I • w := by
  have h : ∀ k, (w k).re • (I • bas n k) - (w k).im • bas n k = (I * w k) • bas n k := by
    intro k
    rw [smul_decomp (I * w k) (bas n k)]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      zero_sub, zero_add, neg_smul]
    abel
  rw [Finset.sum_congr rfl fun k _ => h k]
  simp_rw [mul_smul]
  rw [← Finset.smul_sum, ← vec_expand']

noncomputable section

def lc (F : V n →L[ℝ] ℝ) (j : Fin n) : ℂ :=
  ((F (bas n j) : ℂ) - I * (F (I • bas n j) : ℂ)) / 2

def qc (B : V n →L[ℝ] V n →L[ℝ] ℝ) (j k : Fin n) : ℂ :=
  ((B (bas n j) (bas n k) : ℂ) - (B (I • bas n j) (I • bas n k) : ℂ) -
    I * ((B (bas n j) (I • bas n k) : ℂ) + (B (I • bas n j) (bas n k) : ℂ))) / 8

theorem re_holomorphicLinearTaylorCoeff_sum_eq (F : V n →L[ℝ] ℝ) (a c : Fin n → ℝ) :
    2 * (∑ j, ((a j : ℂ) + (c j : ℂ) * I) * lc F j).re =
      F (∑ k, (a k • bas n k + c k • (I • bas n k))) := by
  simp only [map_sum, map_add, map_smul, smul_eq_mul, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [lc, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.div_ofNat_re,
    Complex.div_ofNat_im, Complex.sub_re, Complex.sub_im]
  ring

theorem re_holomorphicQuadraticTaylorCoeff_sum_eq (B : V n →L[ℝ] V n →L[ℝ] ℝ) (a c : Fin n → ℝ) :
    8 * (∑ j, ∑ k, ((a j : ℂ) + (c j : ℂ) * I) * ((a k : ℂ) + (c k : ℂ) * I) * qc B j k).re =
      B (∑ k, (a k • bas n k + c k • (I • bas n k))) (∑ k, (a k • bas n k + c k • (I • bas n k))) -
      B (∑ k, (a k • (I • bas n k) - c k • bas n k)) (∑ k, (a k • (I • bas n k) - c k • bas n k)) := by
  have e : ∀ x y : Fin n → V n, B (∑ j, x j) (∑ k, y k) = ∑ j, ∑ k, B (x j) (y k) := by
    intro x y
    rw [map_sum B, ContinuousLinearMap.sum_apply]
    simp_rw [map_sum]
  rw [e, e, Complex.re_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [map_add, map_sub, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, qc,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.sub_re, Complex.sub_im]
  ring

end

end GlobalTheory.PluriTaylor

namespace GlobalTheory.PluriTaylor

open Set

variable {n : ℕ}

theorem taylor_two_unif (U K : Set (V n)) (φ : V n → ℝ) (η : ℝ) (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hφ : ContDiffOn ℝ 2 φ U) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, closedBall z δ ⊆ U ∧ ∀ w ∈ closedBall (0 : V n) δ,
      φ (z + w) ≤ φ z + fderiv ℝ φ z w + (1 / 2) * fderiv ℝ (fderiv ℝ φ) z w w + η * ‖w‖ ^ 2 := by
  obtain ⟨δ₀, hδ₀, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  have hK' : IsCompact (cthickening δ₀ K) := hK.cthickening
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ φ) U := hφ.fderiv_of_isOpen hU (by norm_num)
  have h2 : ContinuousOn (fderiv ℝ (fderiv ℝ φ)) U :=
    (h1.fderiv_of_isOpen hU (m := 0) (by norm_num)).continuousOn
  obtain ⟨δ₁, hδ₁, hunif⟩ := Metric.uniformContinuousOn_iff.1
    (hK'.uniformContinuousOn_of_continuous (h2.mono hsub)) η hη
  refine ⟨min δ₀ (δ₁ / 2), lt_min hδ₀ (half_pos hδ₁), fun z hz => ?_⟩
  have hball : closedBall z (min δ₀ (δ₁ / 2)) ⊆ U :=
    (closedBall_subset_closedBall (min_le_left _ _)).trans
      ((closedBall_subset_cthickening hz δ₀).trans hsub)
  refine ⟨hball, fun w hw => ?_⟩
  rw [mem_closedBall, dist_zero_right] at hw
  set f1 := fderiv ℝ φ
  set f2 := fderiv ℝ f1
  have hpt : ∀ t ∈ Icc (0:ℝ) 1, z + t • w ∈ closedBall z (min δ₀ (δ₁ / 2)) := by
    intro t ht
    rw [mem_closedBall, dist_self_add_left, norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans hw
  have hnhds : ∀ t ∈ Icc (0:ℝ) 1, U ∈ 𝓝 (z + t • w) := fun t ht =>
    hU.mem_nhds (hball (hpt t ht))
  have hpath : ∀ t : ℝ, HasDerivAt (fun s : ℝ => z + s • w) w t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const w).const_add z
  have hg : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt (fun s : ℝ => φ (z + s • w)) (f1 (z + t • w) w) t := by
    intro t ht
    have hd : DifferentiableAt ℝ φ (z + t • w) :=
      (hφ.contDiffAt (hnhds t ht)).differentiableAt (by norm_num)
    exact hd.hasFDerivAt.comp_hasDerivAt t (hpath t)
  have hg1 : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun s : ℝ => f1 (z + s • w) w) (f2 (z + t • w) w w) t := by
    intro t ht
    have hd : DifferentiableAt ℝ f1 (z + t • w) :=
      (h1.contDiffAt (hnhds t ht)).differentiableAt (by norm_num)
    have hc : HasDerivAt (fun s : ℝ => f1 (z + s • w)) (f2 (z + t • w) w) t :=
      hd.hasFDerivAt.comp_hasDerivAt t (hpath t)
    have hw0 : HasDerivAt (fun _ : ℝ => w) (0 : V n) t := hasDerivAt_const t w
    have := hc.clm_apply hw0
    simpa using this
  have hclose : ∀ t ∈ Icc (0:ℝ) 1, ‖f2 (z + t • w) - f2 z‖ ≤ η := by
    intro t ht
    have hz' : z ∈ cthickening δ₀ K := self_subset_cthickening K hz
    have hy : z + t • w ∈ cthickening δ₀ K :=
      closedBall_subset_cthickening hz δ₀
        (closedBall_subset_closedBall (min_le_left _ _) (hpt t ht))
    have hd : dist (z + t • w) z < δ₁ := by
      have := hpt t ht
      rw [mem_closedBall] at this
      linarith [min_le_right δ₀ (δ₁ / 2)]
    have := hunif _ hy _ hz' hd
    rw [dist_eq_norm] at this
    exact this.le
  have hud : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt
      (fun s : ℝ => f1 (z + s • w) w - f1 z w - s * f2 z w w)
      (f2 (z + t • w) w w - f2 z w w) (Icc 0 1) t := by
    intro t ht
    have := ((hg1 t ht).sub_const (f1 z w)).sub ((hasDerivAt_id t).mul_const (f2 z w w))
    exact (this.congr_deriv (by simp)).hasDerivWithinAt
  have hbd : ∀ t ∈ Ico (0:ℝ) 1, ‖f2 (z + t • w) w w - f2 z w w‖ ≤ η * ‖w‖ ^ 2 := by
    intro t ht
    have hT := hclose t (Ico_subset_Icc_self ht)
    calc ‖f2 (z + t • w) w w - f2 z w w‖ = ‖(f2 (z + t • w) - f2 z) w w‖ := by
          simp only [ContinuousLinearMap.sub_apply]
      _ ≤ ‖f2 (z + t • w) - f2 z‖ * ‖w‖ * ‖w‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ η * ‖w‖ * ‖w‖ := by gcongr
      _ = η * ‖w‖ ^ 2 := by ring
  have hu : ∀ t ∈ Icc (0:ℝ) 1, ‖f1 (z + t • w) w - f1 z w - t * f2 z w w‖ ≤ η * ‖w‖ ^ 2 := by
    intro t ht
    have := norm_image_sub_le_of_norm_deriv_le_segment' hud hbd t ht
    simp only [zero_smul, add_zero, sub_self, zero_mul, sub_zero] at this
    exact this.trans (mul_le_of_le_one_right (mul_nonneg hη.le (sq_nonneg _)) ht.2)
  have hGd : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt
      (fun s : ℝ => φ (z + s • w) - φ z - s * f1 z w - s ^ 2 / 2 * f2 z w w)
      (f1 (z + t • w) w - f1 z w - t * f2 z w w) (Icc 0 1) t := by
    intro t ht
    have := (((hg t ht).sub_const (φ z)).sub ((hasDerivAt_id t).mul_const (f1 z w))).sub
      (((hasDerivAt_pow 2 t).div_const 2).mul_const (f2 z w w))
    exact (this.congr_deriv (by norm_num)).hasDerivWithinAt
  have hG := norm_image_sub_le_of_norm_deriv_le_segment' hGd
    (fun t ht => hu t (Ico_subset_Icc_self ht)) 1 ⟨zero_le_one, le_rfl⟩
  simp only [one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, sub_self, sub_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, mul_one] at hG
  have hab := (Real.le_norm_self _).trans hG
  linarith

end GlobalTheory.PluriTaylor

namespace GlobalTheory.PluriTaylor

open Complex

theorem taylor_levi_unif : ∀ (n : ℕ) (U K : Set (V n)) (φ : V n → ℝ) (η : ℝ), IsOpen U →
    IsCompact K → K ⊆ U → ContDiffOn ℝ 2 φ U → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K,
      closedBall z δ ⊆ U ∧ ∃ h : V n → ℂ, Differentiable ℂ h ∧ h 0 = 0 ∧
        ∀ w ∈ closedBall (0 : V n) δ, φ (z + w) ≤ φ z + 2 * (h w).re +
          (leviV n (fun v => (φ v : ℂ)) z fun j => w j).re + η * ‖w‖ ^ 2 := by
  intro n U K φ η hU hK hKU hφ hη
  obtain ⟨δ, hδ, hT⟩ := taylor_two_unif U K φ η hU hK hKU hφ hη
  refine ⟨δ, hδ, fun z hz => ⟨(hT z hz).1, ?_⟩⟩
  have hp : ∀ j : Fin n, Differentiable ℂ (fun w : V n => w j) := fun j =>
    (EuclideanSpace.proj (𝕜 := ℂ) j).differentiable
  refine ⟨fun w => ∑ j, w j * lc (fderiv ℝ φ z) j +
      ∑ j, ∑ k, w j * w k * qc (fderiv ℝ (fderiv ℝ φ) z) j k, ?_, ?_, fun w hw => ?_⟩
  · fun_prop
  · simp
  · have hcd : ContDiffAt ℝ 2 φ z := hφ.contDiffAt (hU.mem_nhds (hKU hz))
    have h1 := re_holomorphicLinearTaylorCoeff_sum_eq (fderiv ℝ φ z) (fun j => (w j).re) (fun j => (w j).im)
    have h2 := re_holomorphicQuadraticTaylorCoeff_sum_eq (fderiv ℝ (fderiv ℝ φ) z) (fun j => (w j).re) (fun j => (w j).im)
    have h3 := ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_re_eq hcd (fun j => w j)
    simp only [Complex.re_add_im, sum_re_im_eq, sum_I_eq] at h1 h2 h3
    have h4 := (hT z hz).2 w hw
    simp only [Complex.add_re]
    linarith

end GlobalTheory.PluriTaylor
