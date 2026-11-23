import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogCutoffBoundedPoincareGradient

set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma exists_bound_abs_deriv_smoothTransition_mul_sub_two :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |deriv Real.smoothTransition x| * |x - 2| ≤ M := by
  have hc : Continuous fun x : ℝ => |deriv Real.smoothTransition x| * |x - 2| :=
    ((Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl).abs.mul
      (continuous_id.sub continuous_const).abs
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · have := hM x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
    exact this.trans (le_max_left _ _)
  · have hd : deriv Real.smoothTransition x = 0 := by
      rcases not_and_or.mp hx with h | h
      · have hev : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 0 := by
          filter_upwards [Iio_mem_nhds (not_le.mp h)] with y hy
          exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
        rw [hev.deriv_eq, deriv_const]
      · have hev : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 1 := by
          filter_upwards [Ioi_mem_nhds (not_le.mp h)] with y hy
          exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
        rw [hev.deriv_eq, deriv_const]
    rw [hd, abs_zero, zero_mul]
    exact le_max_right _ _

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma exists_bound_fderiv_logCutoff_mul_norm_mul_log :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (k : ℕ) (z c : ℂ),
      ‖fderiv ℝ (_root_.GlobalTheory.GoodTop.logCutoff k) z c‖ * (‖z‖ * |Real.log ‖z‖|) ≤ M * ‖c‖ := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_abs_deriv_smoothTransition_mul_sub_two
  refine ⟨M, hM0, fun k z c => ?_⟩
  by_cases h0 : z = 0
  · subst h0
    simp only [norm_zero, zero_mul, mul_zero]
    positivity
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hz : 0 < ‖z‖ := norm_pos_iff.mpr h0
  have hev : _root_.GlobalTheory.GoodTop.logCutoff k =ᶠ[𝓝 z]
      fun w => Real.smoothTransition (2 + Real.log ‖w‖ / ((k : ℝ) + 1)) := by
    filter_upwards [isOpen_ne.mem_nhds h0] with w hw
    simp only [_root_.GlobalTheory.GoodTop.logCutoff, if_neg (show w ≠ 0 from hw)]
  set N := fderiv ℝ (fun w : ℂ => ‖w‖) z
  have hn : HasFDerivAt (fun w : ℂ => ‖w‖) N z :=
    ((contDiffAt_norm ℝ (n := 1) h0).differentiableAt one_ne_zero).hasFDerivAt
  have hN : ‖N‖ ≤ 1 := by
    simpa using norm_fderiv_le_of_lipschitz ℝ (f := fun w : ℂ => ‖w‖) (x₀ := z)
      (lipschitzWith_one_norm (E := ℂ))
  have hl := (((Real.hasDerivAt_log hz.ne').div_const ((k : ℝ) + 1)).const_add 2)
  have hg := (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
    (2 + Real.log ‖z‖ / ((k : ℝ) + 1))
  have hs := (hg.hasDerivAt.comp ‖z‖ hl).comp_hasFDerivAt z hn
  have hs' : HasFDerivAt (fun w : ℂ => Real.smoothTransition (2 + Real.log ‖w‖ / ((k : ℝ) + 1)))
      ((deriv Real.smoothTransition (2 + Real.log ‖z‖ / ((k : ℝ) + 1)) *
        (‖z‖⁻¹ / ((k : ℝ) + 1))) • N) z := hs
  rw [hev.fderiv_eq, hs'.fderiv]
  set x := 2 + Real.log ‖z‖ / ((k : ℝ) + 1)
  have hlog : Real.log ‖z‖ = (x - 2) * ((k : ℝ) + 1) := by
    simp only [x]; field_simp; ring
  have hNc : ‖N c‖ ≤ ‖c‖ := (N.le_opNorm c).trans (by simpa using mul_le_mul_of_nonneg_right hN (norm_nonneg c))
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul, Real.norm_eq_abs]
  rw [hlog]
  have e : |deriv Real.smoothTransition x * (‖z‖⁻¹ / ((k : ℝ) + 1)) * N c| *
      (‖z‖ * |(x - 2) * ((k : ℝ) + 1)|) = |deriv Real.smoothTransition x| * |x - 2| * |N c| := by
    rw [abs_mul, abs_mul, abs_mul, abs_div, abs_inv, abs_of_pos hz, abs_of_pos hk]
    field_simp
  rw [e]
  exact mul_le_mul (hM x) (by rw [← Real.norm_eq_abs]; exact hNc) (abs_nonneg _) hM0

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma logCutoff_mem_Icc (k : ℕ) (z : ℂ) :
    0 ≤ _root_.GlobalTheory.GoodTop.logCutoff k z ∧ _root_.GlobalTheory.GoodTop.logCutoff k z ≤ 1 := by
  unfold _root_.GlobalTheory.GoodTop.logCutoff
  split_ifs
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma logCutoff_eq_zero_of_norm_le_exp_neg_two_mul (k : ℕ) {z : ℂ}
    (hz : ‖z‖ ≤ Real.exp (-2 * ((k : ℝ) + 1))) : _root_.GlobalTheory.GoodTop.logCutoff k z = 0 := by
  unfold _root_.GlobalTheory.GoodTop.logCutoff
  split_ifs with h0
  · rfl
  apply Real.smoothTransition.zero_of_nonpos
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlog : Real.log ‖z‖ ≤ -2 * ((k : ℝ) + 1) := by
    rw [← Real.log_exp (-2 * ((k : ℝ) + 1))]
    exact Real.log_le_log (norm_pos_iff.mpr h0) hz
  rw [← sub_nonneg, show 0 - (2 + Real.log ‖z‖ / ((k : ℝ) + 1)) =
    (-2 * ((k : ℝ) + 1) - Real.log ‖z‖) / ((k : ℝ) + 1) by field_simp; ring]
  exact div_nonneg (by linarith) hk.le

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma logCutoff_eq_one_of_exp_le_norm (k : ℕ) {z : ℂ}
    (hz : Real.exp (-((k : ℝ) + 1)) ≤ ‖z‖) : _root_.GlobalTheory.GoodTop.logCutoff k z = 1 := by
  have h0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; exact absurd hz (not_le.mpr (Real.exp_pos _))
  unfold _root_.GlobalTheory.GoodTop.logCutoff
  rw [if_neg h0]
  apply Real.smoothTransition.one_of_one_le
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlog : -((k : ℝ) + 1) ≤ Real.log ‖z‖ := by
    rw [← Real.log_exp (-((k : ℝ) + 1))]
    exact Real.log_le_log (Real.exp_pos _) hz
  rw [← sub_nonneg, show 2 + Real.log ‖z‖ / ((k : ℝ) + 1) - 1 =
    (Real.log ‖z‖ + ((k : ℝ) + 1)) / ((k : ℝ) + 1) by field_simp; ring]
  exact div_nonneg (by linarith) hk.le

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma fderiv_prod_logCutoff_coordVec {n : ℕ} (k : ℕ) (S : Finset (Fin n))
    (v : _root_.ReciprocityTheory.L2DbarEstimates.V n) (b : Fin n) (c : ℂ) :
    fderiv ℝ (fun w : _root_.ReciprocityTheory.L2DbarEstimates.V n => ∏ a ∈ S, _root_.GlobalTheory.GoodTop.logCutoff k (w a)) v
        (c • _root_.GlobalTheory.GoodMetric.coordVec b) =
      if b ∈ S then (∏ a ∈ S.erase b, _root_.GlobalTheory.GoodTop.logCutoff k (v a)) *
        fderiv ℝ (_root_.GlobalTheory.GoodTop.logCutoff k) (v b) c else 0 := by
  have hψ : ∀ z, HasFDerivAt (_root_.GlobalTheory.GoodTop.logCutoff k) (fderiv ℝ (_root_.GlobalTheory.GoodTop.logCutoff k) z) z :=
    fun z => ((_root_.GlobalTheory.GoodTop.contDiff_logCutoff k).differentiable (by simp) z).hasFDerivAt
  have hχ : ContDiff ℝ 1 (fun w : _root_.ReciprocityTheory.L2DbarEstimates.V n => ∏ a ∈ S, _root_.GlobalTheory.GoodTop.logCutoff k (w a)) :=
    contDiff_prod fun a _ =>
      ((_root_.GlobalTheory.GoodTop.contDiff_logCutoff k).of_le (by simp)).comp
        ((EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin n) a).contDiff.restrict_scalars ℝ)
  have hline : HasDerivAt (fun t : ℝ => v + t • (c • _root_.GlobalTheory.GoodMetric.coordVec b))
      (c • _root_.GlobalTheory.GoodMetric.coordVec b) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (c • _root_.GlobalTheory.GoodMetric.coordVec b)).const_add v
  have h1 := ((hχ.differentiable one_ne_zero) v).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline
    (by simp)
  have hcoord : ∀ (t : ℝ) (a : Fin n), (v + t • (c • _root_.GlobalTheory.GoodMetric.coordVec b)) a =
      if a = b then v b + (t : ℂ) * c else v a := by
    intro t a
    simp only [_root_.GlobalTheory.GoodMetric.coordVec, PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.single_apply]
    split_ifs with h
    · subst h; simp [Complex.real_smul]
    · simp
  have hψline : HasDerivAt (fun t : ℝ => _root_.GlobalTheory.GoodTop.logCutoff k (v b + (t : ℂ) * c))
      (fderiv ℝ (_root_.GlobalTheory.GoodTop.logCutoff k) (v b) c) 0 := by
    have hl : HasDerivAt (fun t : ℝ => v b + (t : ℂ) * c) c 0 := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const c).const_add (v b)
    exact (hψ (v b)).comp_hasDerivAt_of_eq 0 hl (by simp)
  split_ifs with hb
  · have h2 : HasDerivAt (fun t : ℝ => ∏ a ∈ S, _root_.GlobalTheory.GoodTop.logCutoff k
        ((v + t • (c • _root_.GlobalTheory.GoodMetric.coordVec b)) a))
        ((∏ a ∈ S.erase b, _root_.GlobalTheory.GoodTop.logCutoff k (v a)) *
          fderiv ℝ (_root_.GlobalTheory.GoodTop.logCutoff k) (v b) c) 0 := by
      have e : (fun t : ℝ => ∏ a ∈ S, _root_.GlobalTheory.GoodTop.logCutoff k
          ((v + t • (c • _root_.GlobalTheory.GoodMetric.coordVec b)) a)) =
          fun t : ℝ => (∏ a ∈ S.erase b, _root_.GlobalTheory.GoodTop.logCutoff k (v a)) *
            _root_.GlobalTheory.GoodTop.logCutoff k (v b + (t : ℂ) * c) := by
        funext t
        rw [← Finset.mul_prod_erase S _ hb, mul_comm, hcoord, if_pos rfl]
        congr 1
        refine Finset.prod_congr rfl fun a ha => ?_
        rw [hcoord, if_neg (Finset.ne_of_mem_erase ha)]
      rw [e]
      exact hψline.const_mul _
    exact h1.unique h2
  · have h2 : HasDerivAt (fun t : ℝ => ∏ a ∈ S, _root_.GlobalTheory.GoodTop.logCutoff k
        ((v + t • (c • _root_.GlobalTheory.GoodMetric.coordVec b)) a)) 0 0 := by
      have e : (fun t : ℝ => ∏ a ∈ S, _root_.GlobalTheory.GoodTop.logCutoff k
          ((v + t • (c • _root_.GlobalTheory.GoodMetric.coordVec b)) a)) =
          fun _ => ∏ a ∈ S, _root_.GlobalTheory.GoodTop.logCutoff k (v a) := by
        funext t
        refine Finset.prod_congr rfl fun a ha => ?_
        rw [hcoord, if_neg (fun h : a = b => hb (h ▸ ha))]
      rw [e]
      exact hasDerivAt_const _ _
    exact h1.unique h2

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in

theorem _root_.GlobalTheory.GoodTop.exists_logCutoff_hyperplanes {n : ℕ} (S : Finset (Fin n)) :
    ∃ (C : ℝ) (χ : ℕ → _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ),
    (∀ k, ContDiff ℝ ∞ (χ k)) ∧ (∀ k v, 0 ≤ χ k v ∧ χ k v ≤ 1) ∧
    (∀ k v, (∃ a ∈ S, v a = 0) → χ k =ᶠ[𝓝 v] fun _ => 0) ∧
    (∀ v : _root_.ReciprocityTheory.L2DbarEstimates.V n, (∀ a ∈ S, v a ≠ 0) → ∀ᶠ k in atTop, χ k =ᶠ[𝓝 v] fun _ => 1) ∧
    ∀ k v b, ‖_root_.GlobalTheory.dbar (fun x => (χ k x : ℂ)) v (_root_.GlobalTheory.GoodMetric.coordVec b)‖ *
      _root_.GlobalTheory.GoodMetric.poinWt S v b ≤ C := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_fderiv_logCutoff_mul_norm_mul_log
  have hproj : ∀ a : Fin n, ContDiff ℝ ∞ fun w : _root_.ReciprocityTheory.L2DbarEstimates.V n => w a := fun a =>
    (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin n) a).contDiff.restrict_scalars ℝ
  have hcont : ∀ a : Fin n, Continuous fun w : _root_.ReciprocityTheory.L2DbarEstimates.V n => w a := fun a => (hproj a).continuous
  refine ⟨M, fun k v => ∏ a ∈ S, _root_.GlobalTheory.GoodTop.logCutoff k (v a), fun k => ?_, fun k v => ?_,
    fun k v hv => ?_, fun v hv => ?_, fun k v b => ?_⟩
  · exact contDiff_prod fun a _ => (_root_.GlobalTheory.GoodTop.contDiff_logCutoff k).comp (hproj a)
  · exact ⟨Finset.prod_nonneg fun a _ => (logCutoff_mem_Icc k _).1,
      Finset.prod_le_one (fun a _ => (logCutoff_mem_Icc k _).1)
        (fun a _ => (logCutoff_mem_Icc k _).2)⟩
  · obtain ⟨a, ha, h0⟩ := hv
    have hopen : IsOpen {w : _root_.ReciprocityTheory.L2DbarEstimates.V n | ‖w a‖ < Real.exp (-2 * ((k : ℝ) + 1))} :=
      isOpen_lt (hcont a).norm continuous_const
    filter_upwards [hopen.mem_nhds (by simp [h0, Real.exp_pos])] with w hw
    exact Finset.prod_eq_zero ha (logCutoff_eq_zero_of_norm_le_exp_neg_two_mul k (le_of_lt hw))
  · have hone : ∀ a ∈ S, ∀ᶠ k : ℕ in atTop, ∀ᶠ w in 𝓝 v, _root_.GlobalTheory.GoodTop.logCutoff k (w a) = 1 := by
      intro a ha
      have hr : 0 < ‖v a‖ / 2 := by have := norm_pos_iff.mpr (hv a ha); positivity
      obtain ⟨N, hN⟩ := exists_nat_gt (-Real.log (‖v a‖ / 2))
      have hopen : IsOpen {w : _root_.ReciprocityTheory.L2DbarEstimates.V n | ‖v a‖ / 2 < ‖w a‖} :=
        isOpen_lt continuous_const (hcont a).norm
      have hvm : v ∈ {w : _root_.ReciprocityTheory.L2DbarEstimates.V n | ‖v a‖ / 2 < ‖w a‖} := by
        have := norm_pos_iff.mpr (hv a ha)
        show ‖v a‖ / 2 < ‖v a‖
        linarith
      filter_upwards [Filter.eventually_ge_atTop N] with k hk
      filter_upwards [hopen.mem_nhds hvm] with w hw
      apply logCutoff_eq_one_of_exp_le_norm
      refine le_trans ?_ hw.le
      rw [← Real.exp_log hr]
      apply Real.exp_le_exp.mpr
      have : (N : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    filter_upwards [(Filter.eventually_all_finset S).2 hone] with k hk
    filter_upwards [(Filter.eventually_all_finset S).2 hk] with w hw
    exact Finset.prod_eq_one hw
  · set χk := fun w : _root_.ReciprocityTheory.L2DbarEstimates.V n => ∏ a ∈ S, _root_.GlobalTheory.GoodTop.logCutoff k (w a) with hχk
    have hd : DifferentiableAt ℝ χk v :=
      ((contDiff_prod fun a _ => (_root_.GlobalTheory.GoodTop.contDiff_logCutoff k).comp (hproj a)).differentiable
        (by simp)) v
    have hF : ∀ w, fderiv ℝ (fun x => (χk x : ℂ)) v w = ((fderiv ℝ χk v w : ℝ) : ℂ) := by
      intro w
      have hc := Complex.ofRealCLM.hasFDerivAt.comp v hd.hasFDerivAt
      rw [show (fun x => (χk x : ℂ)) = Complex.ofRealCLM ∘ χk from rfl, hc.fderiv]
      rfl
    rw [_root_.GlobalTheory.dbar_apply, hF, hF]
    have h1 := fderiv_prod_logCutoff_coordVec k S v b 1
    have hI := fderiv_prod_logCutoff_coordVec k S v b Complex.I
    rw [one_smul] at h1
    rw [h1, hI]
    unfold _root_.GlobalTheory.GoodMetric.poinWt
    split_ifs with hb
    · set P := ∏ a ∈ S.erase b, _root_.GlobalTheory.GoodTop.logCutoff k (v a)
      have hP : |P| ≤ 1 := by
        rw [abs_of_nonneg (Finset.prod_nonneg fun a _ => (logCutoff_mem_Icc k _).1)]
        exact Finset.prod_le_one (fun a _ => (logCutoff_mem_Icc k _).1)
          (fun a _ => (logCutoff_mem_Icc k _).2)
      have hw : 0 ≤ ‖v b‖ * |Real.log ‖v b‖| := by positivity
      have b1 := hM k (v b) 1
      have bI := hM k (v b) Complex.I
      rw [norm_one, mul_one] at b1
      rw [Complex.norm_I, mul_one] at bI
      rw [Real.norm_eq_abs] at b1 bI
      calc ‖(1 / 2 : ℂ) • (((P * fderiv ℝ (_root_.GlobalTheory.GoodTop.logCutoff k) (v b) 1 : ℝ) : ℂ) +
            Complex.I • ((P * fderiv ℝ (_root_.GlobalTheory.GoodTop.logCutoff k) (v b) Complex.I : ℝ) : ℂ))‖ *
            (‖v b‖ * |Real.log ‖v b‖|)
          ≤ (1 / 2) * (|fderiv ℝ (_root_.GlobalTheory.GoodTop.logCutoff k) (v b) 1| +
              |fderiv ℝ (_root_.GlobalTheory.GoodTop.logCutoff k) (v b) Complex.I|) * (‖v b‖ * |Real.log ‖v b‖|) := by
            refine mul_le_mul_of_nonneg_right ?_ hw
            rw [norm_smul, norm_div, norm_one, Complex.norm_two]
            refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (by norm_num)
            rw [norm_smul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
              Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
            exact add_le_add (mul_le_of_le_one_left (abs_nonneg _) hP)
              (mul_le_of_le_one_left (abs_nonneg _) hP)
        _ ≤ M := by nlinarith
    · simpa using hM0

end GlobalTheory.GoodTop
