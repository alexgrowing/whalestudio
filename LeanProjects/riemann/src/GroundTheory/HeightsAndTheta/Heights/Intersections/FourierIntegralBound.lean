import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeN
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial MeasureTheory Topology Filter Set
open scoped ContDiff
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential MIntegrable locDens)

section Lemmas

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem eval_tsmul_of_isMultiHomog {s : MRing ι ℂ} {a : K → ℕ} (hs : IsMultiHomog s a)
    (c : K → ℂ) (z : MCone ι) :
    eval (tsmul c z) s = (∏ k, c k ^ a k) * eval z s := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw := hs (mem_support_iff.mp hd)
  have hk : ∀ k, ∑ i, d ⟨k, i⟩ = a k := by
    intro k
    rw [← hw]
    simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_sigma,
      GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight, Pi.single_apply]
    rw [Finset.sum_eq_single k (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  have hprod : ∏ v, tsmul c z v ^ d v = (∏ k, c k ^ a k) * ∏ v, z v ^ d v := by
    simp only [tsmul, mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ d ⟨k, i⟩ = c k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hk k]
  rw [hprod]
  ring

theorem secNorm_tsmul {P : Ideal (MRing ι ℂ)} {A : HLine ι} {s : MRing ι ℂ} (hs : IsFormSec P A s)
    {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : MCone ι) :
    secNorm A s (tsmul c z) = secNorm A s z := by
  obtain ⟨a, ha, hsa, -⟩ := hs
  unfold secNorm
  rw [eval_tsmul_of_isMultiHomog hsa c z]
  have hh : A.h (tsmul c z) = (∏ k, ‖c k‖ ^ A.a k) * A.h z := A.smul c z hc
  have hpos : 0 < ∏ k, ‖c k‖ ^ A.a k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hc k)) _
  have hn : ‖∏ k, c k ^ a k‖ = ∏ k, ‖c k‖ ^ A.a k := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_pow, ha k, zpow_natCast]
  rw [hh, norm_mul, hn, mul_div_mul_left _ _ hpos.ne']

theorem abs_log_div_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    |Real.log (a / b)| ≤ |Real.log a| + |Real.log b| := by
  rcases ha.eq_or_lt with h | h
  · subst h; simp
  · rw [Real.log_div h.ne' hb.ne']
    exact abs_sub _ _

namespace Res

variable {P : Ideal (MRing ι ℂ)} {e : ℕ} (R : Res ι P e)

theorem isGoodAtlas : R.R.IsGoodAtlas R.atlas := R.R.exists_atlas.choose_spec

omit [Fintype K] in

theorem liftAt_mem {x y : R.R.M} (hy : y ∈ R.R.src (R.idx x)) : R.liftAt x y ∈ zPts P :=
  R.R.lift_mem _ y hy

omit [Fintype K] in

theorem sameOrbit_liftAt {x x' y : R.R.M} (hy : y ∈ R.R.src (R.idx x))
    (hy' : y ∈ R.R.src (R.idx x')) :
    ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ R.liftAt x y = tsmul c (R.liftAt x' y) :=
  R.R.compat _ _ y ⟨hy, hy'⟩

omit [Fintype K] in

theorem continuousOn_liftAt (x : R.R.M) (q : Σ k, ι k) :
    ContinuousOn (fun y => R.liftAt x y q) (R.R.src (R.idx x)) := by
  have h : ContinuousOn (R.R.coord (R.idx x)) (R.R.src (R.idx x)) :=
    continuousOn_iff_continuous_domRestrict.mpr (R.R.isEmbedding _).continuous
  exact (MvPolynomial.continuous_eval (R.R.lift (R.idx x) q)).comp_continuousOn h

theorem analyticAt_liftAt (x : R.R.M) (q : Σ k, ι k) (j : Fin R.atlas.n) {u : Fin e → ℂ}
    (hu : u ∈ (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x)) :
    AnalyticAt ℂ (fun v => R.liftAt x ((R.atlas.chart j).symm v) q) u :=
  R.isGoodAtlas.1 (R.idx x) (R.R.lift (R.idx x) q) j u hu

theorem analyticAt_liftAt_pi (x : R.R.M) (j : Fin R.atlas.n) {u : Fin e → ℂ}
    (hu : u ∈ (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x)) :
    AnalyticAt ℂ (fun v => R.liftAt x ((R.atlas.chart j).symm v)) u :=
  analyticAt_pi_iff.mpr fun q => R.analyticAt_liftAt x q j hu

theorem isPotential_pot {φ : MCone ι → ℝ} (hφ : IsSmoothPot P φ) :
    IsPotential R.atlas (R.pot φ) := by
  classical
  obtain ⟨⟨a, ha⟩, hloc⟩ := hφ
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  ·
    intro u hu
    have hu' : u ∈ (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x) := hu
    have hγ : AnalyticAt ℂ (fun v => R.liftAt x ((R.atlas.chart j).symm v)) u :=
      R.analyticAt_liftAt_pi x j hu'
    obtain ⟨U, hU, G, hG, hGφ⟩ := hloc _ (R.liftAt_mem hu'.2)
    have hGc : ContDiffAt ℝ ∞ (G ∘ fun v => R.liftAt x ((R.atlas.chart j).symm v)) u :=
      (hG.contDiffAt hU).comp u ((hγ.contDiffAt (n := ∞)).restrict_scalars ℝ)
    refine hGc.contDiffWithinAt.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (hγ.continuousAt.preimage_mem_nhds hU)] with v hv hvU
      exact hGφ _ ⟨hvU, R.liftAt_mem hv.2⟩
    · exact hGφ _ ⟨mem_of_mem_nhds hU, R.liftAt_mem hu'.2⟩
  ·
    have hy' : y ∈ R.R.src (R.idx x) ∩ R.R.src (R.idx x') := hy
    choose p hp using (R.liftAt_mem hy'.2).1
    obtain ⟨c, hc, hcy⟩ := R.sameOrbit_liftAt hy'.1 hy'.2
    have hnum : ∀ k, R.liftAt x y ⟨k, p k⟩ ≠ 0 := fun k => by
      rw [hcy]; exact mul_ne_zero (hc k) (hp k)
    have hr : ∀ k, R.liftAt x y ⟨k, p k⟩ / R.liftAt x' y ⟨k, p k⟩ ≠ 0 :=
      fun k => div_ne_zero (hnum k) (hp k)
    have hO : IsOpen (R.R.src (R.idx x) ∩ R.R.src (R.idx x')) :=
      (R.R.isOpen_alt_bis _).inter (R.R.isOpen_alt_bis _)
    let q : K → R.R.M → ℂ := fun k z => R.liftAt x z ⟨k, p k⟩ / R.liftAt x' z ⟨k, p k⟩ /
      (R.liftAt x y ⟨k, p k⟩ / R.liftAt x' y ⟨k, p k⟩)
    let W : Set R.R.M := {z | z ∈ R.R.src (R.idx x) ∩ R.R.src (R.idx x') ∧
      ∀ k, R.liftAt x' z ⟨k, p k⟩ ≠ 0 ∧ q k z ∈ Complex.slitPlane}
    have hW : IsOpen W := by
      refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
      have hn : ∀ k, ContinuousAt (fun z => R.liftAt x z ⟨k, p k⟩) z := fun k =>
        ((R.continuousOn_liftAt x _).mono inter_subset_left).continuousAt (hO.mem_nhds hz.1)
      have hd : ∀ k, ContinuousAt (fun z => R.liftAt x' z ⟨k, p k⟩) z := fun k =>
        ((R.continuousOn_liftAt x' _).mono inter_subset_right).continuousAt (hO.mem_nhds hz.1)
      filter_upwards [hO.mem_nhds hz.1, eventually_all.mpr fun k => (hd k).eventually_ne (hz.2 k).1,
        eventually_all.mpr fun k => (((hn k).div (hd k) (hz.2 k).1).div_const _).eventually_mem
          (Complex.isOpen_slitPlane.mem_nhds (hz.2 k).2)] with w h1 h2 h3
      exact ⟨h1, fun k => ⟨h2 k, h3 k⟩⟩
    have hyW : y ∈ W := by
      refine ⟨hy', fun k => ⟨hp k, ?_⟩⟩
      have : q k y = 1 := div_self (hr k)
      rw [this]
      exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simp))
    let G : R.R.M → ℂ := fun z => ∑ k, ((a k : ℝ) : ℂ) *
      (Complex.log (q k z) + ((Real.log ‖R.liftAt x y ⟨k, p k⟩ / R.liftAt x' y ⟨k, p k⟩‖ : ℝ) : ℂ))
    refine ⟨W, hW, hyW, G, fun j y' hy'' => ?_, fun z hz => ?_⟩
    ·
      have hz : (R.atlas.chart j).symm y' ∈ W := hy''.2
      have hterm : ∀ k, AnalyticAt ℂ (fun y'' => ((a k : ℝ) : ℂ) *
          (Complex.log (q k ((R.atlas.chart j).symm y'')) +
            ((Real.log ‖R.liftAt x y ⟨k, p k⟩ / R.liftAt x' y ⟨k, p k⟩‖ : ℝ) : ℂ))) y' := by
        intro k
        have hn : AnalyticAt ℂ (fun y'' => R.liftAt x ((R.atlas.chart j).symm y'') ⟨k, p k⟩) y' :=
          R.analyticAt_liftAt x _ j ⟨hy''.1, hz.1.1⟩
        have hd : AnalyticAt ℂ (fun y'' => R.liftAt x' ((R.atlas.chart j).symm y'') ⟨k, p k⟩) y' :=
          R.analyticAt_liftAt x' _ j ⟨hy''.1, hz.1.2⟩
        have hq : AnalyticAt ℂ (fun y'' => q k ((R.atlas.chart j).symm y'')) y' :=
          (hn.div hd (hz.2 k).1).div analyticAt_const (hr k)
        have hl : AnalyticAt ℂ (Complex.log ∘ fun y'' => q k ((R.atlas.chart j).symm y'')) y' :=
          AnalyticAt.comp (f := fun y'' => q k ((R.atlas.chart j).symm y''))
            (analyticAt_clog (hz.2 k).2) hq
        exact analyticAt_const.mul (hl.add analyticAt_const)
      exact Finset.analyticAt_fun_sum _ fun k _ => hterm k
    ·
      have hzW : z ∈ W := hz.1.1
      obtain ⟨c', hc', hcz⟩ := R.sameOrbit_liftAt hzW.1.1 hzW.1.2
      have hterm : ∀ k, Real.log ‖q k z‖ +
          Real.log ‖R.liftAt x y ⟨k, p k⟩ / R.liftAt x' y ⟨k, p k⟩‖ = Real.log ‖c' k‖ := by
        intro k
        have hqz : q k z = c' k / (R.liftAt x y ⟨k, p k⟩ / R.liftAt x' y ⟨k, p k⟩) := by
          simp only [q]
          rw [hcz]
          simp only [tsmul]
          rw [mul_div_assoc, div_self (hzW.2 k).1, mul_one]
        rw [hqz, norm_div, Real.log_div (norm_ne_zero_iff.mpr (hc' k))
          (norm_ne_zero_iff.mpr (hr k))]
        ring
      show φ (R.liftAt x z) - φ (R.liftAt x' z) = (G z).re
      rw [hcz, ha c' hc' _ (R.liftAt_mem hzW.1.2), add_sub_cancel_left]
      simp only [G, Complex.re_sum, Complex.re_ofReal_mul, Complex.add_re, Complex.log_re,
        Complex.ofReal_re]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hterm k]

end Res

end Lemmas

theorem S4.proof : S4.Statement := by
  intro K _ _ ι _ P e R φ A s _ hφ hA hs j Kc hK hKc
  refine LocallyIntegrableOn.integrableOn_compact_subset ?_ hK hKc
  intro u0 hu0
  set x0 := (R.atlas.chart j).symm u0
  set V := (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x0) with hVdef
  have hV : IsOpen V := (R.atlas.chart j).isOpen_inter_preimage_symm (R.R.isOpen_alt_bis _)
  have hu0V : u0 ∈ V := ⟨hu0, R.mem_src_idx x0⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV u0 hu0V
  set B := Metric.closedBall u0 (r / 2) with hBdef
  have hBV : B ⊆ V := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hBc : IsCompact B := isCompact_closedBall _ _
  have hBm : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  refine ⟨B, mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds _ (by linarith)), ?_⟩
  set γ : (Fin e → ℂ) → MCone ι := fun u => R.liftAt x0 ((R.atlas.chart j).symm u) with hγdef
  have hγ : ∀ u ∈ V, AnalyticAt ℂ γ u := fun u hu => R.analyticAt_liftAt_pi x0 j hu
  have hγZ : ∀ u ∈ V, γ u ∈ zPts P := fun u hu => R.liftAt_mem hu.2
  set f : (Fin e → ℂ) → ℂ := fun u => eval (γ u) s with hfdef
  have hf : AnalyticOnNhd ℂ f V := fun u hu =>
    ReciprocityTheory.AnForm.R.analyticAt_eval_of_pi (fun q => analyticAt_pi_iff.mp (hγ u hu) q) s
  set H : (Fin e → ℂ) → ℝ := fun u => A.h (γ u) with hHdef
  have hHpos : ∀ u ∈ V, 0 < H u := fun u hu => A.pos _ (hγZ u hu).1
  have hHc : ContinuousOn H V := by
    intro u hu
    obtain ⟨U, hU, G, hG, hGe⟩ := hA (γ u) (hγZ u hu)
    have hcont : ContinuousAt (fun u' => Real.exp (G (γ u'))) u :=
      Real.continuous_exp.continuousAt.comp
        ((hG.continuousOn.continuousAt hU).comp (hγ u hu).continuousAt)
    refine (hcont.congr ?_).continuousWithinAt
    filter_upwards [hV.mem_nhds hu, (hγ u hu).continuousAt.preimage_mem_nhds hU] with v hv hvU
    show Real.exp (G (γ v)) = A.h (γ v)
    rw [← hGe _ ⟨hvU, hγZ v hv⟩]
    exact Real.exp_log (hHpos v hv)
  have hF : ∀ u ∈ V, secNorm A s (R.pt ((R.atlas.chart j).symm u)) = Real.log (‖f u‖ / H u) := by
    intro u hu
    obtain ⟨c, hc, hcz⟩ := R.sameOrbit_liftAt (x := (R.atlas.chart j).symm u) (x' := x0)
      (R.mem_src_idx _) hu.2
    show secNorm A s (R.liftAt _ _) = _
    rw [hcz, secNorm_tsmul hs hc]
    rfl
  have hDc : ContinuousOn (locDens R.atlas (fun i => R.pot (φ i)) j) B :=
    (ReciprocityTheory.AnForm.M.locDensCont R.atlas _ (fun i => R.isPotential_pot (hφ i)) j).mono
      (hBV.trans inter_subset_left)
  obtain ⟨M, hM⟩ := hBc.exists_bound_of_continuousOn hDc
  have hlogf : IntegrableOn (fun u => Real.log ‖f u‖) B :=
    (ReciprocityTheory.ChartRestriction.G.Geo.logAbsLocInt' e V f hV hf).integrableOn_compact_subset hBV hBc
  have hlogH : IntegrableOn (fun u => Real.log (H u)) B :=
    ((hHc.mono hBV).log fun u hu => (hHpos u (hBV hu)).ne').integrableOn_compact hBc
  have hfc : ContinuousOn f B := fun u hu => (hf u (hBV hu)).continuousAt.continuousWithinAt
  have hmeas : AEStronglyMeasurable (fun u => Real.log (‖f u‖ / H u) *
      locDens R.atlas (fun i => R.pot (φ i)) j u) (volume.restrict B) := by
    have h1 : AEStronglyMeasurable (fun u => ‖f u‖ / H u) (volume.restrict B) :=
      (hfc.norm.div (hHc.mono hBV) fun u hu => (hHpos u (hBV hu)).ne').aestronglyMeasurable hBm
    exact (Real.measurable_log.comp_aemeasurable h1.aemeasurable).aestronglyMeasurable.mul
      (hDc.aestronglyMeasurable hBm)
  have hint : IntegrableOn (fun u => Real.log (‖f u‖ / H u) *
      locDens R.atlas (fun i => R.pot (φ i)) j u) B := by
    refine Integrable.mono' ((hlogf.norm.add hlogH.norm).mul_const M) hmeas ?_
    refine ae_restrict_of_forall_mem hBm fun u hu => ?_
    rw [norm_mul]
    have hb := abs_log_div_le' (norm_nonneg (f u)) (hHpos u (hBV hu))
    simp only [Real.norm_eq_abs] at hb ⊢
    exact mul_le_mul hb (hM u hu) (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  refine hint.congr_fun (fun u hu => ?_) hBm
  simp only
  rw [hF u (hBV hu)]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
