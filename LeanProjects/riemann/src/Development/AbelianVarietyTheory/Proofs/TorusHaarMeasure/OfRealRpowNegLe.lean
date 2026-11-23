import Mathlib
import Development.AbelianVarietyTheory.Definitions.UpperBounds.SumNormSqWPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PnormInvStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfB

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up.DivMetricPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in

theorem _root_.GlobalTheory.Up.DivMetricPf.exp_neg_phla {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom)
    (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) :
    Real.exp (-_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.phla X la x) = X.nfac la x ^ 2 := by
  have hpos := _root_.ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.nfac_pos X hx la
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.phla
  rw [show -(-2 * Real.log (X.nfac la x)) = Real.log (X.nfac la x) + Real.log (X.nfac la x) by
    ring, Real.exp_add, Real.exp_log hpos]
  ring

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in

theorem _root_.GlobalTheory.Up.DivMetricPf.pnorm_rmul (hN : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacRmulStatement (E := E)) {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    {P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : X.IsSec la P) {x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom)
    (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r) :
    X.pnorm la P (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) = X.pnorm la P x :=
  _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.pnorm_rmul X la P hP.2.1 x hx b hb

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in

theorem _root_.GlobalTheory.Up.DivMetricPf.pnorm_lact (hN : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement (E := E)) {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    {P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : X.IsSec la P) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.pnorm la P (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) = X.pnorm la P x := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement at hN
  change ‖P (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x)‖ * X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) = ‖P x‖ * X.nfac la x
  rw [hP.2.2 γ hγ x hx, norm_mul, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.chi_norm X la hγ, one_mul, hN r X la γ hγ x hx]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in

theorem _root_.GlobalTheory.Up.DivMetricPf.measurable_cut {f : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℝ}
    (hf : ContinuousOn f X.dom) :
    Measurable (X.dom.indicator fun x => ENNReal.ofReal (f x)) := by
  have hc : ContinuousOn (fun x => ((Real.sqrt (f x) : ℝ) : ℂ)) X.dom :=
    Complex.continuous_ofReal.comp_continuousOn (Real.continuous_sqrt.comp_continuousOn hf)
  have key : ∀ y, ENNReal.ofReal (‖((Real.sqrt (f y) : ℝ) : ℂ)‖ ^ 2) = ENNReal.ofReal (f y) := by
    intro y
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rcases le_total 0 (f y) with h | h
    · rw [Real.sq_sqrt h]
    · rw [Real.sqrt_eq_zero'.mpr h, ENNReal.ofReal_of_nonpos h]
      simp
  have hm := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.phiF_meas X (W := 1) hc measurable_one
  convert hm using 1
  funext y
  classical
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.phiF
  simp only [Pi.one_apply, mul_one]
  by_cases hy : y ∈ X.dom
  · rw [Set.indicator_of_mem hy, Set.piecewise_eq_of_mem _ _ _ hy, key]
  · rw [Set.indicator_of_notMem hy, Set.piecewise_eq_of_notMem _ _ _ hy]
    rfl

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in

theorem _root_.GlobalTheory.Up.DivMetricPf.exists_sum_le {N : ℕ} {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    {P : Fin N → _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : ∀ k, X.IsBddSec la (P k)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ X.dom, ∑ k, X.pnorm la (P k) x ^ 2 ≤ C := by
  choose C hC using fun k => (hP k).2
  refine ⟨1 + ∑ k, C k ^ 2, by positivity, fun x hx => ?_⟩
  have hle : ∀ k, X.pnorm la (P k) x ^ 2 ≤ C k ^ 2 := by
    intro k
    have h0 : 0 ≤ X.pnorm la (P k) x := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
      exact mul_nonneg (norm_nonneg _) (_root_.ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.nfac_pos X hx la).le
    exact pow_le_pow_left₀ h0 (hC k x hx) 2
  calc ∑ k, X.pnorm la (P k) x ^ 2 ≤ ∑ k, C k ^ 2 := Finset.sum_le_sum fun k _ => hle k
    _ ≤ 1 + ∑ k, C k ^ 2 := by linarith

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in

theorem _root_.GlobalTheory.Up.DivMetricPf.ofReal_rpow_neg_le {a C t : ℝ} (hC : 0 < C) (h : a ≤ C) (ht : 0 ≤ t) :
    ENNReal.ofReal (C ^ (-t)) ≤ ENNReal.ofReal a ^ (-t) := by
  rcases lt_or_ge 0 a with ha | ha
  · rw [ENNReal.ofReal_rpow_of_pos ha]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos ha h (by linarith))
  · rw [ENNReal.ofReal_of_nonpos ha]
    rcases ht.lt_or_eq with ht | ht
    · rw [ENNReal.zero_rpow_of_neg (by linarith)]
      exact le_top
    · subst ht
      simp

variable (Xa : ArchInM X) (Fl : FlatM X Xa) (n : ℕ)

theorem measurable_Wdiv : Measurable (Wdiv X Xa Fl n) := by
  have h1 := measurable_cut ((ExtFPf.nfac_contOn X Xa.Fp).pow 2)
  have h2 : Measurable (X.dom.indicator fun x => ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2)) :=
    measurable_cut (continuousOn_finsetSum _ fun k _ =>
      (Xa.w_van k).1.1.1.1.continuousOn.norm.pow 2)
  have h3 : Measurable (X.dom.indicator fun x => ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2)) :=
    measurable_cut (continuousOn_finsetSum _ fun k _ =>
      (Fl.s_van k).1.1.1.1.continuousOn.norm.pow 2)
  have h := (h1.mul (h2.pow_const (-(1 / 2 : ℝ)))).mul (h3.pow_const (-((n : ℝ) - 1 / 2)))
  convert h using 1
  funext x
  by_cases hx : x ∈ X.dom
  · rw [Wdiv_of_mem Xa Fl n hx, exp_neg_phla hx]
    simp only [Pi.mul_apply, Set.indicator_of_mem hx, Pi.pow_apply]
  · rw [Wdiv_of_notMem Xa Fl n hx]
    simp only [Pi.mul_apply, Set.indicator_of_notMem hx, zero_mul]

theorem Wdiv_rmul (hN : NfacRmulStatement (E := E)) {x b : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hb : b ∈ Bor X.Ψ r) :
    Wdiv X Xa Fl n (rmul x b) =
      Wdiv X Xa Fl n x / ENNReal.ofReal (‖bchar (Xa.Fp + n • Xa.L) b‖ ^ 2) := by
  have hxb := OntoS.dom_rmul X hx hb
  have h0 : 0 < ‖bchar (Xa.Fp + n • Xa.L) b‖ ^ 2 :=
    pow_pos (norm_pos_iff.2 (OntoE.bchar_ne X _ hb)) 2
  rw [Wdiv_eq_pnorm Xa Fl n hxb, Wdiv_eq_pnorm Xa Fl n hx, exp_neg_phla hx, exp_neg_phla hxb,
    hN r X _ x hx b hb]
  simp only [fun k => pnorm_rmul hN (Xa.w_van k).1.1.1 hx hb,
    fun k => pnorm_rmul hN (Fl.s_van k).1.1.1 hx hb]
  rw [mul_pow, inv_pow, ENNReal.ofReal_mul (inv_nonneg.2 h0.le), ENNReal.ofReal_inv_of_pos h0,
    ENNReal.div_eq_inv_mul]
  simp only [mul_assoc]

theorem Wdiv_lact (hN : NfacLactStatement (E := E)) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) : Wdiv X Xa Fl n (lact γ x) = Wdiv X Xa Fl n x := by
  have hxb := OntoS.dom_lact X hγ hx
  rw [Wdiv_eq_pnorm Xa Fl n hxb, Wdiv_eq_pnorm Xa Fl n hx, exp_neg_phla hx, exp_neg_phla hxb,
    hN r X _ γ hγ x hx]
  simp only [fun k => pnorm_lact hN (Xa.w_van k).1.1.1 hγ hx,
    fun k => pnorm_lact hN (Fl.s_van k).1.1.1 hγ hx]

theorem Wdiv_lower (hn : 1 ≤ n) : WLower X (Xa.Fp + n • Xa.L) (Wdiv X Xa Fl n) := by
  obtain ⟨A, hA, hAw⟩ := exists_sum_le fun k => (Xa.w_van k).1.1
  obtain ⟨B, hB, hBs⟩ := exists_sum_le fun k => (Fl.s_van k).1.1
  have hn' : 0 ≤ (n : ℝ) - 1 / 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hA' := Real.rpow_pos_of_pos hA (-(1 / 2 : ℝ))
  have hB' := Real.rpow_pos_of_pos hB (-((n : ℝ) - 1 / 2))
  refine ⟨A ^ (-(1 / 2 : ℝ)) * B ^ (-((n : ℝ) - 1 / 2)), mul_pos hA' hB', fun x hx => ?_⟩
  rw [Wdiv_eq_pnorm Xa Fl n hx, mul_comm, ← mul_assoc,
    ENNReal.ofReal_mul (mul_pos (Real.exp_pos _) hA').le, ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact mul_le_mul' (mul_le_mul' le_rfl (ofReal_rpow_neg_le hA (hAw x hx) (by norm_num)))
    (ofReal_rpow_neg_le hB (hBs x hx) hn')

theorem divMetric_of :
    (NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E)) →
      GlobalTheory.Up.DivMetric (E := E) := by
  intro h r X Xa Fl n hn
  exact ⟨⟨measurable_Wdiv Xa Fl n, fun x hx b hb => Wdiv_rmul Xa Fl n h.1 hx hb,
    fun γ hγ x hx => Wdiv_lact Xa Fl n h.2.1 hγ hx⟩, Wdiv_lower Xa Fl n hn,
    fun x hx hs => Wdiv_eq_exp Xa Fl n hx hs⟩

end GlobalTheory.Up.DivMetricPf
