import Mathlib
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz

open FourierTransform MeasureTheory Filter Topology
open scoped ContDiff Nat SchwartzMap

noncomputable section

namespace GlobalTheory.GaussCutoff

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def cutErr (c : ℝ) (y : E) : ℂ := GroundTheory.Global.gaussianSchwartz E (c • y) - 1

theorem contDiff_cutErr (c : ℝ) : ContDiff ℝ ∞ (cutErr (E := E) c) :=
  (((GroundTheory.Global.gaussianSchwartz E).smooth ⊤).comp (contDiff_const_smul c)).sub contDiff_const

theorem norm_cutErr_le (c : ℝ) (y : E) : ‖cutErr c y‖ ≤ Real.pi * c ^ 2 * ‖y‖ ^ 2 := by
  unfold cutErr
  rw [GroundTheory.Global.gaussianSchwartz_apply]
  have hx : ‖c • y‖ ^ 2 = c ^ 2 * ‖y‖ ^ 2 := by rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [hx]
  set a := Real.pi * c ^ 2 * ‖y‖ ^ 2 with ha_def
  have ha : 0 ≤ a := by positivity
  have h1 : Real.exp (-Real.pi * (c ^ 2 * ‖y‖ ^ 2)) = Real.exp (-a) := by
    congr 1; rw [ha_def]; ring
  have he : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 ha)
  rw [h1, show ((Real.exp (-a) : ℝ) : ℂ) - 1 = ((Real.exp (-a) - 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  linarith [Real.add_one_le_exp (-a)]

theorem norm_iteratedFDeriv_cutErr_le (c : ℝ) {j : ℕ} (hj : j ≠ 0) (y : E) :
    ‖iteratedFDeriv ℝ j (cutErr c) y‖ ≤
      |c| ^ j * SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E) := by
  set g := GroundTheory.Global.gaussianSchwartz E with hg
  set L : E →L[ℝ] E := c • ContinuousLinearMap.id ℝ E with hL
  have hgL : ContDiff ℝ ∞ ((g : E → ℂ) ∘ L) := (g.smooth ⊤).comp L.contDiff
  have hfun : cutErr (E := E) c = ((g : E → ℂ) ∘ L) - fun _ => (1 : ℂ) := by
    funext z; simp [cutErr, hL, hg]
  rw [hfun, iteratedFDeriv_sub_apply (hgL.contDiffAt.of_le (by exact_mod_cast le_top)) contDiffAt_const,
    iteratedFDeriv_const_of_ne hj, Pi.zero_apply, sub_zero,
    L.iteratedFDeriv_comp_right (g.smooth ⊤) y (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hLn : ‖L‖ ≤ |c| := by
    rw [hL]; refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs]; exact mul_le_of_le_one_right (abs_nonneg c) ContinuousLinearMap.norm_id_le
  have hD : ‖iteratedFDeriv ℝ j g (L y)‖ ≤ SchwartzMap.seminorm ℝ 0 j g := by
    simpa using SchwartzMap.le_seminorm ℝ 0 j g (L y)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hLn j) hD (norm_nonneg _)
    (pow_nonneg (abs_nonneg c) j)

theorem norm_iteratedFDeriv_cutErr_le' (c : ℝ) (hc : |c| ≤ 1) (j : ℕ) (y : E) :
    ‖iteratedFDeriv ℝ j (cutErr c) y‖ ≤
      |c| * (Real.pi + SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E)) * (1 + ‖y‖) ^ 2 := by
  have hS : 0 ≤ SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E) := apply_nonneg _ _
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hc0 : 0 ≤ |c| := abs_nonneg c
  have hpi := Real.pi_pos
  have h1 : 1 ≤ (1 + ‖y‖) ^ 2 := one_le_pow₀ (by linarith)
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [norm_iteratedFDeriv_zero]
    refine (norm_cutErr_le c y).trans ?_
    have hc2 : c ^ 2 ≤ |c| := by rw [← sq_abs]; nlinarith
    have hy2 : ‖y‖ ^ 2 ≤ (1 + ‖y‖) ^ 2 := by nlinarith
    calc Real.pi * c ^ 2 * ‖y‖ ^ 2 ≤ Real.pi * |c| * (1 + ‖y‖) ^ 2 := by gcongr
      _ = |c| * Real.pi * (1 + ‖y‖) ^ 2 := by ring
      _ ≤ _ := by gcongr; linarith
  · refine (norm_iteratedFDeriv_cutErr_le c hj.ne' y).trans ?_
    have hcj : |c| ^ j ≤ |c| := pow_le_of_le_one hc0 hc hj.ne'
    calc |c| ^ j * SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E)
        ≤ |c| * SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E) := by gcongr
      _ ≤ |c| * (Real.pi + SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E)) * 1 := by
          rw [mul_one]; gcongr; linarith
      _ ≤ _ := by gcongr

theorem cut_bound (h : 𝓢(E, ℂ)) (k n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, |c| ≤ 1 → ∀ y : E,
    ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => cutErr c y * h y) y‖ ≤ |c| * K := by
  set S : ℕ → ℝ := fun i => SchwartzMap.seminorm ℝ 0 i (GroundTheory.Global.gaussianSchwartz E) with hS
  set P := (Finset.Iic (k + 2, n)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) h with hP_def
  have hP : 0 ≤ P := apply_nonneg _ _
  have hS0 : ∀ i, 0 ≤ S i := fun i => apply_nonneg _ _
  have hpi := Real.pi_pos
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (Real.pi + S i) * (2 ^ (k + 2) * P),
    Finset.sum_nonneg fun i _ => by have := hS0 i; positivity, fun c hc y => ?_⟩
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hL := norm_iteratedFDeriv_mul_le (contDiff_cutErr (E := E) c) (h.smooth ⊤) y (n := n)
    (by exact_mod_cast le_top)
  calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => cutErr c y * h y) y‖
      ≤ ‖y‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (cutErr c) y‖ *
          ‖iteratedFDeriv ℝ (n - i) h y‖ := by gcongr
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (‖iteratedFDeriv ℝ i (cutErr c) y‖ *
          (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖)) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((|c| * (Real.pi + S i)) *
          ((1 + ‖y‖) ^ 2 * (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := norm_iteratedFDeriv_cutErr_le' c hc i y
        have h0 : 0 ≤ ‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖ := by positivity
        have e : |c| * (Real.pi + S i) * ((1 + ‖y‖) ^ 2 * (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖)) =
          (|c| * (Real.pi + S i) * (1 + ‖y‖) ^ 2) * (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖) := by ring
        rw [e]; gcongr
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((|c| * (Real.pi + S i)) * (2 ^ (k + 2) * P)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hS0i := hS0 i
        have hX : (1 + ‖y‖) ^ 2 * (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖) ≤ 2 ^ (k + 2) * P := by
          calc (1 + ‖y‖) ^ 2 * (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖)
              ≤ (1 + ‖y‖) ^ 2 * ((1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖) := by
                gcongr; linarith
            _ = (1 + ‖y‖) ^ (k + 2) * ‖iteratedFDeriv ℝ (n - i) h y‖ := by ring
            _ ≤ 2 ^ (k + 2) * P :=
                SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k + 2, n)) le_rfl
                  (Nat.sub_le n i) h y
        gcongr
    _ = |c| * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (Real.pi + S i) * (2 ^ (k + 2) * P) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring

def cutMap (h : 𝓢(E, ℂ)) (c : ℝ) (hc : |c| ≤ 1) : 𝓢(E, ℂ) where
  toFun y := cutErr c y * h y
  smooth' := (contDiff_cutErr c).mul (h.smooth ⊤)
  decay' k n := by
    obtain ⟨K, -, hK⟩ := cut_bound h k n
    exact ⟨|c| * K, hK c hc⟩

theorem cutMap_apply (h : 𝓢(E, ℂ)) (c : ℝ) (hc : |c| ≤ 1) (y : E) :
    cutMap h c hc y = cutErr c y * h y := rfl

end GlobalTheory.GaussCutoff

open GlobalTheory.GaussCutoff in

theorem GlobalTheory.GaussCutoff.mem_closure_gauss_mul (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (h : SchwartzMap E ℂ) :
    h ∈ closure {u : SchwartzMap E ℂ | ∃ b : ℝ, 0 < b ∧ ∀ y, u y = Complex.exp (-((b * ‖y‖ ^ 2 : ℝ) : ℂ)) * h y} := by
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨s, r, hr, hsub⟩ := ((schwartz_withSeminorms ℝ E ℂ).mem_nhds_iff h U).1 hU
  choose K hK0 hK using fun m : ℕ × ℕ => cut_bound h m.1 m.2
  set M := ∑ m ∈ s, K m with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun m _ => hK0 m
  set c := min 1 (r / (2 * (M + 1))) with hc_def
  have hcpos : 0 < c := lt_min one_pos (by positivity)
  have hc1 : |c| ≤ 1 := by rw [abs_of_pos hcpos]; exact min_le_left _ _
  have hcr : c * (M + 1) ≤ r / 2 := by
    have := min_le_right 1 (r / (2 * (M + 1)))
    rw [← hc_def] at this
    calc c * (M + 1) ≤ r / (2 * (M + 1)) * (M + 1) := by gcongr
      _ = r / 2 := by field_simp
  refine ⟨h + cutMap h c hc1, hsub ?_, Real.pi * c ^ 2, by positivity, fun y => ?_⟩
  · rw [Seminorm.mem_ball, add_sub_cancel_left]
    refine Seminorm.finset_sup_apply_lt hr fun m hm => ?_
    have h1 : SchwartzMap.seminorm ℝ m.1 m.2 (cutMap h c hc1) ≤ |c| * K m :=
      SchwartzMap.seminorm_le_bound ℝ m.1 m.2 _ (mul_nonneg (abs_nonneg c) (hK0 m)) (hK m c hc1)
    have h2 : K m ≤ M := Finset.single_le_sum (fun m _ => hK0 m) hm
    show SchwartzMap.seminorm ℝ m.1 m.2 (cutMap h c hc1) < r
    rw [abs_of_pos hcpos] at h1
    nlinarith
  · rw [add_apply, cutMap_apply, cutErr, GroundTheory.Global.gaussianSchwartz_apply, Complex.ofReal_exp]
    have e : -Real.pi * ‖c • y‖ ^ 2 = -(Real.pi * c ^ 2 * ‖y‖ ^ 2) := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
    rw [e]; push_cast; ring
