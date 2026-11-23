import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLogLogCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Filter Topology
open scoped ContDiff

noncomputable section

theorem smoothTransition_eventually_const {x : ℝ} (hx : x ∉ Set.Icc (0 : ℝ) 1) :
    ∃ c : ℝ, Real.smoothTransition =ᶠ[𝓝 x] fun _ => c := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with h | h
  · refine ⟨0, ?_⟩
    filter_upwards [Iio_mem_nhds h] with y hy
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
  · refine ⟨1, ?_⟩
    filter_upwards [Ioi_mem_nhds h] with y hy
    exact Real.smoothTransition.one_of_one_le (le_of_lt hy)

theorem smoothTransition_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |deriv Real.smoothTransition x| ≤ C ∧
      |deriv (deriv Real.smoothTransition) x| ≤ C := by
  have hsm : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  obtain ⟨-, h1⟩ := contDiff_infty_iff_deriv.1 hsm
  obtain ⟨-, h2⟩ := contDiff_infty_iff_deriv.1 h1
  obtain ⟨C1, hC1⟩ := isCompact_Icc.exists_bound_of_continuousOn (h1.continuous.continuousOn (s := Set.Icc (0 : ℝ) 1))
  obtain ⟨C2, hC2⟩ := isCompact_Icc.exists_bound_of_continuousOn (h2.continuous.continuousOn (s := Set.Icc (0 : ℝ) 1))
  refine ⟨max (max C1 C2) 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · have a := hC1 x hx
    have b := hC2 x hx
    rw [Real.norm_eq_abs] at a b
    exact ⟨a.trans ((le_max_left _ _).trans (le_max_left _ _)),
      b.trans ((le_max_right _ _).trans (le_max_left _ _))⟩
  · obtain ⟨c, hc⟩ := smoothTransition_eventually_const hx
    have hd := hc.deriv
    have e1 : deriv Real.smoothTransition x = 0 := by rw [hd.eq_of_nhds]; simp
    have e2 : deriv (deriv Real.smoothTransition) x = 0 := by rw [hd.deriv_eq]; simp
    rw [e1, e2, abs_zero]
    exact ⟨le_max_right _ _, le_max_right _ _⟩

theorem logLogStep_arith {C c t p q f v w : ℝ} (hC0 : 0 ≤ C) (hc : 1 ≤ c) (ht : t ≠ 0) (hp : |p| ≤ C)
    (hq : |q| ≤ C) (hf : |f| ≤ 1) (hv : v = -(2 * (t⁻¹ / c))) (hw : w = -(2 * (-(t ^ 2)⁻¹ / c))) :
    |q * v * v + p * w| ≤ (6 * C + 4 * C ^ 2) / (c * t ^ 2) ∧
      |p * v * (p * v) + f * (q * v * v + p * w)| ≤ (6 * C + 4 * C ^ 2) / (c * t ^ 2) := by
  have hc0 : 0 < c := by linarith
  have hD : 0 < c * t ^ 2 := by positivity
  have hvv : v * v ≤ 4 / (c * t ^ 2) := by
    have e : v * v = 4 / (c * t ^ 2) / c := by rw [hv]; field_simp; ring
    rw [e]; exact div_le_self (by positivity) hc
  have hvv0 : 0 ≤ v * v := mul_self_nonneg v
  have hw' : |w| = 2 / (c * t ^ 2) := by
    have e : w = 2 / (c * t ^ 2) := by rw [hw]; field_simp
    rw [e, abs_of_pos (by positivity)]
  have h1 : |q * v * v + p * w| ≤ 6 * C / (c * t ^ 2) := by
    calc |q * v * v + p * w| ≤ |q * v * v| + |p * w| := abs_add_le _ _
      _ = |q| * (v * v) + |p| * |w| := by rw [mul_assoc, abs_mul q, abs_of_nonneg hvv0, abs_mul p]
      _ ≤ C * (4 / (c * t ^ 2)) + C * (2 / (c * t ^ 2)) := by rw [hw']; gcongr
      _ = 6 * C / (c * t ^ 2) := by ring
  have h2 : p * v * (p * v) ≤ 4 * C ^ 2 / (c * t ^ 2) := by
    calc p * v * (p * v) = |p| ^ 2 * (v * v) := by rw [sq_abs]; ring
      _ ≤ C ^ 2 * (4 / (c * t ^ 2)) := by gcongr
      _ = 4 * C ^ 2 / (c * t ^ 2) := by ring
  have hK : 6 * C / (c * t ^ 2) ≤ (6 * C + 4 * C ^ 2) / (c * t ^ 2) := by
    gcongr; nlinarith
  refine ⟨h1.trans hK, ?_⟩
  calc |p * v * (p * v) + f * (q * v * v + p * w)|
      ≤ |p * v * (p * v)| + |f * (q * v * v + p * w)| := abs_add_le _ _
    _ ≤ 4 * C ^ 2 / (c * t ^ 2) + 1 * (6 * C / (c * t ^ 2)) := by
      rw [abs_of_nonneg (mul_self_nonneg (p * v)), abs_mul]; gcongr
    _ = (6 * C + 4 * C ^ 2) / (c * t ^ 2) := by ring

theorem logLogStep_deriv2_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 1 ≤ c → ∀ t : ℝ, t < 0 →
      ContDiffAt ℝ 2 (fun x => cutStep (Real.log (-x) / c)) t ∧
      ContDiffAt ℝ 2 (fun x => cutStep (Real.log (-x) / c) ^ 2 / 2) t ∧
      |deriv (deriv fun x => cutStep (Real.log (-x) / c)) t| ≤ K / (c * t ^ 2) ∧
      |deriv (deriv fun x => cutStep (Real.log (-x) / c) ^ 2 / 2) t| ≤ K / (c * t ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := smoothTransition_deriv_bound
  refine ⟨6 * C + 4 * C ^ 2, by positivity, fun c hc t ht => ?_⟩
  have hc0 : 0 < c := by linarith
  set σ := Real.smoothTransition with hσdef
  have hsm : ContDiff ℝ ∞ σ := Real.smoothTransition.contDiff
  obtain ⟨hd0, h1⟩ := contDiff_infty_iff_deriv.1 hsm
  obtain ⟨hd1, -⟩ := contDiff_infty_iff_deriv.1 h1
  let u : ℝ → ℝ := fun x => 2 - 2 * (Real.log (-x) / c)
  let u' : ℝ → ℝ := fun x => -(2 * (x⁻¹ / c))
  let u'' : ℝ → ℝ := fun x => -(2 * (-(x ^ 2)⁻¹ / c))
  have hu : ∀ x, x < 0 → HasDerivAt u (u' x) x := by
    intro x hx
    have hl : HasDerivAt (fun x => Real.log (-x)) x⁻¹ x := by
      have := (hasDerivAt_neg x).log (by simpa using hx.ne)
      rwa [neg_div_neg_eq, one_div] at this
    exact ((hl.div_const c).const_mul 2).const_sub 2
  have hu' : ∀ x, x < 0 → HasDerivAt u' (u'' x) x := fun x hx =>
    (((hasDerivAt_inv hx.ne).div_const c).const_mul 2).neg
  let F : ℝ → ℝ := fun x => cutStep (Real.log (-x) / c)
  let G : ℝ → ℝ := fun x => deriv σ (u x) * u' x
  have hF : ∀ x, x < 0 → HasDerivAt F (G x) x := fun x hx =>
    (hd0 (u x)).hasDerivAt.comp x (hu x hx)
  have hG : HasDerivAt G (deriv (deriv σ) (u t) * u' t * u' t + deriv σ (u t) * u'' t) t :=
    ((hd1 (u t)).hasDerivAt.comp t (hu t ht)).mul (hu' t ht)
  have evF : deriv F =ᶠ[𝓝 t] G := by
    filter_upwards [Iio_mem_nhds ht] with x hx
    exact (hF x hx).deriv
  have hF2 : deriv (deriv F) t = deriv (deriv σ) (u t) * u' t * u' t + deriv σ (u t) * u'' t :=
    (hG.congr_of_eventuallyEq evF).deriv
  have hH : ∀ x, x < 0 → HasDerivAt (fun x => F x ^ 2 / 2) (F x * G x) x := by
    intro x hx
    have := ((hF x hx).fun_mul (hF x hx)).div_const 2
    exact (this.congr_deriv (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by ring)
  have evH : deriv (fun x => F x ^ 2 / 2) =ᶠ[𝓝 t] fun x => F x * G x := by
    filter_upwards [Iio_mem_nhds ht] with x hx
    exact (hH x hx).deriv
  have hH2 : deriv (deriv fun x => F x ^ 2 / 2) t =
      G t * G t + F t * (deriv (deriv σ) (u t) * u' t * u' t + deriv σ (u t) * u'' t) :=
    (((hF t ht).fun_mul hG).congr_of_eventuallyEq evH).deriv
  have hucd : ContDiffAt ℝ 2 u t :=
    contDiffAt_const.sub (contDiffAt_const.mul ((contDiffAt_id.neg.log (by simpa using ht.ne)).div_const c))
  have hFcd : ContDiffAt ℝ 2 F t := (Real.smoothTransition.contDiffAt (n := 2)).comp t hucd
  have hf : |F t| ≤ 1 := by
    show |Real.smoothTransition (u t)| ≤ 1
    exact abs_le.2 ⟨by linarith [Real.smoothTransition.nonneg (u t)], Real.smoothTransition.le_one (u t)⟩
  obtain ⟨b1, b2⟩ := logLogStep_arith (p := deriv σ (u t)) (q := deriv (deriv σ) (u t)) hC0 hc ht.ne
    (hC _).1 (hC _).2 hf rfl rfl
  refine ⟨hFcd, (hFcd.pow 2).div_const 2, ?_, ?_⟩
  · rw [show deriv (deriv fun x => cutStep (Real.log (-x) / c)) t = _ from hF2]; exact b1
  · rw [show deriv (deriv fun x => cutStep (Real.log (-x) / c) ^ 2 / 2) t = _ from hH2]; exact b2

end

end GroundTheory.Heights₂.Heights
