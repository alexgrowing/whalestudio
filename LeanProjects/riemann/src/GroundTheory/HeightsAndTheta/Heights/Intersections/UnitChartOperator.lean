import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P : Ideal (GroundTheory.Heights₂.Heights.NumbersDVR.MRing ι ℂ)} {e : ℕ}

theorem res_isGoodAtlas (R : Res ι P e) : R.R.IsGoodAtlas R.atlas :=
  R.R.exists_atlas.choose_spec

theorem res_holo (R : Res ι P e) (x : R.R.M) (q : Σ k, ι k) :
    R.atlas.HoloOn (R.R.src (R.idx x)) (fun y => R.liftAt x y q) :=
  (res_isGoodAtlas R).1 (R.idx x) (R.R.lift (R.idx x) q)

omit [Fintype K] in

theorem res_mem (R : Res ι P e) (x : R.R.M) {y : R.R.M} (hy : y ∈ R.R.src (R.idx x)) :
    R.liftAt x y ∈ ReciprocityTheory.AnForm.R.conePts P :=
  R.R.lift_mem (R.idx x) y hy

omit [Fintype K] in

theorem res_compat (R : Res ι P e) (x x' : R.R.M) {y : R.R.M} (hy : y ∈ R.R.src (R.idx x))
    (hy' : y ∈ R.R.src (R.idx x')) :
    ReciprocityTheory.AnForm.R.SameOrbit (R.liftAt x y) (R.liftAt x' y) :=
  R.R.compat _ _ y ⟨hy, hy'⟩

theorem res_eq_of_sameOrbit {g : MCone ι → ℝ}
    (hg : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → ∀ z ∈ zPts P, g (tsmul c z) = g z) (R : Res ι P e)
    (x : R.R.M) {y : R.R.M} (hy : y ∈ R.R.src (R.idx x)) : g (R.liftAt x y) = g (R.pt y) := by
  obtain ⟨c, hc, hcy⟩ := res_compat R x y hy (R.mem_src_idx y)
  rw [hcy]
  exact hg c hc (R.pt y) (res_mem R y (R.mem_src_idx y))

theorem res_contDiffOn_lift (R : Res ι P e) (x : R.R.M) (j : Fin R.atlas.n) :
    ContDiffOn ℝ ∞ (fun y => R.liftAt x ((R.atlas.chart j).symm y))
      ((R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x)) :=
  contDiffOn_pi.mpr fun q => ((res_holo R x q j).contDiffOn_of_completeSpace).restrict_scalars ℝ

theorem res_contDiffOn_comp (R : Res ι P e) {g : MCone ι → ℝ} (hg : IsLocSmooth P g)
    (x : R.R.M) (j : Fin R.atlas.n) :
    ContDiffOn ℝ ∞ (fun y => g (R.liftAt x ((R.atlas.chart j).symm y)))
      ((R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x)) := by
  have hS : IsOpen ((R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x)) :=
    (R.atlas.chart j).isOpen_inter_preimage_symm (R.R.isOpen_alt_bis _)
  have hF := res_contDiffOn_lift R x j
  refine contDiffOn_of_locally_contDiffOn fun y hy => ?_
  obtain ⟨U, hU, G, hG, hgG⟩ := hg _ (res_mem R x hy.2)
  have hpre : (fun y => R.liftAt x ((R.atlas.chart j).symm y)) ⁻¹' U ∈ 𝓝 y :=
    (hF.continuousOn.continuousAt (hS.mem_nhds hy)).preimage_mem_nhds hU
  obtain ⟨u, hus, huo, hyu⟩ := mem_nhds_iff.mp hpre
  refine ⟨u, huo, hyu, ?_⟩
  refine (hG.comp (hF.mono Set.inter_subset_left) fun y' hy' => hus hy'.2).congr fun y' hy' => ?_
  exact hgG _ ⟨hus hy'.2, res_mem R x hy'.1.2⟩

theorem res_smooth (R : Res ι P e) {u : MCone ι → ℝ} (hu : IsSmoothFn P u) :
    R.atlas.Smooth (fun x => u (R.pt x)) := by
  intro j
  refine contDiffOn_of_locally_contDiffOn fun y hy => ?_
  set x0 := (R.atlas.chart j).symm y
  refine ⟨(R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x0),
    (R.atlas.chart j).isOpen_inter_preimage_symm (R.R.isOpen_alt_bis _), ⟨hy.1, R.mem_src_idx x0⟩, ?_⟩
  refine ((res_contDiffOn_comp R hu.2 x0 j).mono Set.inter_subset_right).congr fun y' hy' => ?_
  exact (res_eq_of_sameOrbit hu.1 R x0 hy'.2.2).symm

theorem res_continuousOn_lift (R : Res ι P e) (x : R.R.M) (p : Σ k, ι k) :
    ContinuousOn (fun z => R.liftAt x z p) (R.R.src (R.idx x)) := by
  intro z hz
  obtain ⟨j, hj⟩ := R.atlas.cover z
  have hzt : R.atlas.chart j z ∈ (R.atlas.chart j).target := (R.atlas.chart j).map_source hj
  have hc : ContinuousAt ((fun z => R.liftAt x z p) ∘ (R.atlas.chart j).symm)
      (R.atlas.chart j z) :=
    (res_holo R x p j _ ⟨hzt, by rwa [Set.mem_preimage, (R.atlas.chart j).left_inv hj]⟩).continuousAt
  have h := ((R.atlas.chart j).symm.continuousAt_iff_continuousAt_comp_right
    (f := fun z => R.liftAt x z p) (x := z) (by simpa using hj)).mpr (by simpa using hc)
  exact h.continuousWithinAt

theorem res_isPotential (R : Res ι P e) {L : HLine ι} (hL : IsSmoothMetric P L) :
    IsPotential R.atlas (R.pot (logH L)) := by
  classical
  refine ⟨fun x j => res_contDiffOn_comp R hL x j, fun x x' y hy => ?_⟩
  have hy' : y ∈ R.R.src (R.idx x) ∩ R.R.src (R.idx x') := hy
  choose p hp using (res_mem R x' hy'.2).1
  obtain ⟨c, hc, hcy⟩ := res_compat R x x' hy'.1 hy'.2
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
      ((res_continuousOn_lift R x _).mono Set.inter_subset_left).continuousAt (hO.mem_nhds hz.1)
    have hd : ∀ k, ContinuousAt (fun z => R.liftAt x' z ⟨k, p k⟩) z := fun k =>
      ((res_continuousOn_lift R x' _).mono Set.inter_subset_right).continuousAt (hO.mem_nhds hz.1)
    filter_upwards [hO.mem_nhds hz.1, eventually_all.mpr fun k => (hd k).eventually_ne (hz.2 k).1,
      eventually_all.mpr fun k => (((hn k).div (hd k) (hz.2 k).1).div_const _).eventually_mem
        (Complex.isOpen_slitPlane.mem_nhds (hz.2 k).2)] with w h1 h2 h3
    exact ⟨h1, fun k => ⟨h2 k, h3 k⟩⟩
  have hyW : y ∈ W := by
    refine ⟨hy', fun k => ⟨hp k, ?_⟩⟩
    have : q k y = 1 := div_self (hr k)
    rw [this]
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simp))
  let G : R.R.M → ℂ := fun z => ∑ k, ((L.a k : ℝ) : ℂ) *
    (Complex.log (q k z) + ((Real.log ‖R.liftAt x y ⟨k, p k⟩ / R.liftAt x' y ⟨k, p k⟩‖ : ℝ) : ℂ))
  refine ⟨W, hW, hyW, G, fun j y' hy'' => ?_, fun z hz => ?_⟩
  ·
    have hz : (R.atlas.chart j).symm y' ∈ W := hy''.2
    have hterm : ∀ k, AnalyticAt ℂ (fun y'' => ((L.a k : ℝ) : ℂ) *
        (Complex.log (q k ((R.atlas.chart j).symm y'')) +
          ((Real.log ‖R.liftAt x y ⟨k, p k⟩ / R.liftAt x' y ⟨k, p k⟩‖ : ℝ) : ℂ))) y' := by
      intro k
      have hn : AnalyticAt ℂ (fun y'' => R.liftAt x ((R.atlas.chart j).symm y'') ⟨k, p k⟩) y' :=
        res_holo R x _ j y' ⟨hy''.1, hz.1.1⟩
      have hd : AnalyticAt ℂ (fun y'' => R.liftAt x' ((R.atlas.chart j).symm y'') ⟨k, p k⟩) y' :=
        res_holo R x' _ j y' ⟨hy''.1, hz.1.2⟩
      have hq : AnalyticAt ℂ (fun y'' => q k ((R.atlas.chart j).symm y'')) y' :=
        (hn.div hd (hz.2 k).1).div analyticAt_const (hr k)
      have hl : AnalyticAt ℂ (Complex.log ∘ fun y'' => q k ((R.atlas.chart j).symm y'')) y' :=
        AnalyticAt.comp (f := fun y'' => q k ((R.atlas.chart j).symm y''))
          (analyticAt_clog (hz.2 k).2) hq
      exact analyticAt_const.mul (hl.add analyticAt_const)
    exact Finset.analyticAt_fun_sum _ fun k _ => hterm k
  ·
    have hzW : z ∈ W := hz.1.1
    obtain ⟨c', hc', hcz⟩ := res_compat R x x' hzW.1.1 hzW.1.2
    have hpos : 0 < L.h (R.liftAt x' z) := L.pos _ (res_mem R x' hzW.1.2).1
    have hprod : (∏ k, ‖c' k‖ ^ L.a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc' k))
    have hterm : ∀ k, Real.log ‖q k z‖ +
        Real.log ‖R.liftAt x y ⟨k, p k⟩ / R.liftAt x' y ⟨k, p k⟩‖ = Real.log ‖c' k‖ := by
      intro k
      have hqz : q k z = c' k / (R.liftAt x y ⟨k, p k⟩ / R.liftAt x' y ⟨k, p k⟩) := by
        simp only [q]
        rw [hcz, mul_div_assoc, div_self (hzW.2 k).1, mul_one]
      rw [hqz, norm_div, Real.log_div (norm_ne_zero_iff.mpr (hc' k))
        (norm_ne_zero_iff.mpr (hr k))]
      ring
    show Real.log (L.h (R.liftAt x z)) - Real.log (L.h (R.liftAt x' z)) = (G z).re
    rw [hcz, L.smul c' _ hc', Real.log_mul hprod hpos.ne', add_sub_cancel_right,
      Real.log_prod fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc' k))]
    simp only [G, Complex.re_sum, Complex.re_ofReal_mul, Complex.add_re, Complex.log_re,
      Complex.ofReal_re]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hterm k, Real.log_zpow]

theorem res_int_cons (R : Res ι P (e + 1)) {u : MCone ι → ℝ} (hu : IsSmoothFn P u)
    (φ : Fin e → MCone ι → ℝ) (g : MCone ι → ℝ) :
    R.int (Fin.cons u φ) g = mInt R.atlas (Fin.cons (LocPot.ofFun fun x => u (R.pt x))
      fun i => R.pot (φ i)) (fun x => g (R.pt x)) := by
  have hc : (fun j => R.pot ((Fin.cons u φ : Fin (e + 1) → MCone ι → ℝ) j)) =
      Fin.cons (R.pot u) fun i => R.pot (φ i) := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j <;> simp
  unfold Res.int
  rw [hc]
  refine ReciprocityTheory.ChartRestriction.G.Geo.mInt_congr _
    (ReciprocityTheory.ChartRestriction.G.Geo.locDens_cons_congr _ _ fun j y hy => ?_) fun _ => rfl
  set x0 := (R.atlas.chart j).symm y
  filter_upwards [((R.atlas.chart j).isOpen_inter_preimage_symm (R.R.isOpen_alt_bis (R.idx x0))).mem_nhds
    ⟨hy, R.mem_src_idx x0⟩] with y' hy'
  exact res_eq_of_sameOrbit hu.1 R x0 hy'.2

theorem S3.proof : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.S3.Statement := by
  intro K _ _ ι _ P e L v w _ hR hL hv hw
  have key : ∀ R : Res ι P (e + 1), R.int (Fin.cons w fun j => logH (L j)) v =
      R.int (Fin.cons v fun j => logH (L j)) w := by
    intro R
    rw [res_int_cons R hw, res_int_cons R hv]
    exact byPartsSymm R.atlas _ _ (res_smooth R hv) (res_smooth R hw) _
      fun i => res_isPotential R (hL i)
  unfold zInt
  rw [dif_pos hR, dif_pos hR]
  exact key _

end GroundTheory.Heights₂.Heights.Inter
