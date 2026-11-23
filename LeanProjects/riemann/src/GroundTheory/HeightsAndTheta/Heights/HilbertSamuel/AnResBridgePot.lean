import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedB
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithRes
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial ReciprocityTheory.AnForm.M Filter Topology MeasureTheory
open scoped ContDiff

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {P J : Ideal (MRing ι)} {e : ℕ}

def potOf (R : AnRes P J e) (L : HermLine ι) : LocPot R.X where
  U := R.U
  isOpen_U := R.isOpen_U
  mem_U := R.mem_U
  φ x y := Real.log (L.h (R.lift x y))

theorem contDiffOn_lift (R : AnRes P J e) (x : R.X) (j : Fin R.A.n) :
    ContDiffOn ℝ ∞ (fun y => R.lift x ((R.A.chart j).symm y))
      ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) :=
  contDiffOn_pi.mpr fun p => ((R.holo x p j).contDiffOn_of_completeSpace).restrict_scalars ℝ

theorem contDiffOn_potOf (R : AnRes P J e) {L : HermLine ι} (hL : IsSmoothHerm L) (x : R.X)
    (j : Fin R.A.n) :
    ContDiffOn ℝ ∞ (fun y => Real.log (L.h (R.lift x ((R.A.chart j).symm y))))
      ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) := by
  have hmc : ∀ y ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x,
      R.lift x ((R.A.chart j).symm y) ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    fun y hy => (R.mem x _ hy.2).1
  refine (hL.comp (contDiffOn_lift R x j) hmc).log fun y hy => ?_
  exact (L.pos _ (hmc y hy)).ne'

theorem smoothOn_potOf (R : AnRes P J e) {L : HermLine ι} (hL : IsSmoothHerm L) (x : R.X) :
    R.A.SmoothOn ((potOf R L).U x) ((potOf R L).φ x) :=
  fun j => contDiffOn_potOf R hL x j

theorem continuousOn_lift (R : AnRes P J e) (x : R.X) (p : Σ k, ι k) :
    ContinuousOn (fun z => R.lift x z p) (R.U x) := by
  intro z hz
  obtain ⟨j, hj⟩ := R.A.cover z
  have hzt : R.A.chart j z ∈ (R.A.chart j).target := (R.A.chart j).map_source hj
  have hc : ContinuousAt ((fun z => R.lift x z p) ∘ (R.A.chart j).symm) (R.A.chart j z) :=
    (R.holo x p j _ ⟨hzt, by rwa [Set.mem_preimage, (R.A.chart j).left_inv hj]⟩).continuousAt
  have h := ((R.A.chart j).symm.continuousAt_iff_continuousAt_comp_right
    (f := fun z => R.lift x z p) (x := z) (by simpa using hj)).mpr (by simpa using hc)
  exact h.continuousWithinAt

theorem isPotential_potOf (R : AnRes P J e) {L : HermLine ι} (hL : IsSmoothHerm L) :
    IsPotential R.A (potOf R L) := by
  classical
  refine ⟨smoothOn_potOf R hL, fun x x' y hy => ?_⟩
  have hy' : y ∈ R.U x ∩ R.U x' := hy
  choose p hp using (R.mem x' y hy'.2).1
  obtain ⟨c, hc, hcy⟩ := R.compat x x' y hy'
  have hnum : ∀ k, R.lift x y ⟨k, p k⟩ ≠ 0 := fun k => by
    rw [hcy]; exact mul_ne_zero (hc k) (hp k)
  have hr : ∀ k, R.lift x y ⟨k, p k⟩ / R.lift x' y ⟨k, p k⟩ ≠ 0 :=
    fun k => div_ne_zero (hnum k) (hp k)
  have hO : IsOpen (R.U x ∩ R.U x') := (R.isOpen_U x).inter (R.isOpen_U x')

  let q : K → R.X → ℂ := fun k z => R.lift x z ⟨k, p k⟩ / R.lift x' z ⟨k, p k⟩ /
    (R.lift x y ⟨k, p k⟩ / R.lift x' y ⟨k, p k⟩)
  let W : Set R.X := {z | z ∈ R.U x ∩ R.U x' ∧ ∀ k, R.lift x' z ⟨k, p k⟩ ≠ 0 ∧ q k z ∈ Complex.slitPlane}
  have hW : IsOpen W := by
    refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
    have hn : ∀ k, ContinuousAt (fun z => R.lift x z ⟨k, p k⟩) z := fun k =>
      ((continuousOn_lift R x _).mono Set.inter_subset_left).continuousAt (hO.mem_nhds hz.1)
    have hd : ∀ k, ContinuousAt (fun z => R.lift x' z ⟨k, p k⟩) z := fun k =>
      ((continuousOn_lift R x' _).mono Set.inter_subset_right).continuousAt (hO.mem_nhds hz.1)
    filter_upwards [hO.mem_nhds hz.1, eventually_all.mpr fun k => (hd k).eventually_ne (hz.2 k).1,
      eventually_all.mpr fun k => (((hn k).div (hd k) (hz.2 k).1).div_const _).eventually_mem
        (Complex.isOpen_slitPlane.mem_nhds (hz.2 k).2)] with w h1 h2 h3
    exact ⟨h1, fun k => ⟨h2 k, h3 k⟩⟩
  have hyW : y ∈ W := by
    refine ⟨hy', fun k => ⟨hp k, ?_⟩⟩
    have : q k y = 1 := div_self (hr k)
    rw [this]
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simp))
  let G : R.X → ℂ := fun z => ∑ k, ((L.a k : ℝ) : ℂ) *
    (Complex.log (q k z) + ((Real.log ‖R.lift x y ⟨k, p k⟩ / R.lift x' y ⟨k, p k⟩‖ : ℝ) : ℂ))
  refine ⟨W, hW, hyW, G, fun j y' hy'' => ?_, fun z hz => ?_⟩
  ·
    have hz : (R.A.chart j).symm y' ∈ W := hy''.2
    have hterm : ∀ k, AnalyticAt ℂ (fun y'' => ((L.a k : ℝ) : ℂ) *
        (Complex.log (q k ((R.A.chart j).symm y'')) +
          ((Real.log ‖R.lift x y ⟨k, p k⟩ / R.lift x' y ⟨k, p k⟩‖ : ℝ) : ℂ))) y' := by
      intro k
      have hn : AnalyticAt ℂ (fun y'' => R.lift x ((R.A.chart j).symm y'') ⟨k, p k⟩) y' :=
        R.holo x _ j y' ⟨hy''.1, hz.1.1⟩
      have hd : AnalyticAt ℂ (fun y'' => R.lift x' ((R.A.chart j).symm y'') ⟨k, p k⟩) y' :=
        R.holo x' _ j y' ⟨hy''.1, hz.1.2⟩
      have hq : AnalyticAt ℂ (fun y'' => q k ((R.A.chart j).symm y'')) y' :=
        (hn.div hd (hz.2 k).1).div analyticAt_const (hr k)
      have hl : AnalyticAt ℂ (Complex.log ∘ fun y'' => q k ((R.A.chart j).symm y'')) y' :=
        AnalyticAt.comp (f := fun y'' => q k ((R.A.chart j).symm y'')) (analyticAt_clog (hz.2 k).2) hq
      exact analyticAt_const.mul (hl.add analyticAt_const)
    exact Finset.analyticAt_fun_sum _ fun k _ => hterm k
  ·
    have hzW : z ∈ W := hz.1.1
    obtain ⟨c', hc', hcz⟩ := R.compat x x' z hzW.1
    have hpos : 0 < L.h (R.lift x' z) := L.pos _ (R.mem x' z hzW.1.2).1
    have hprod : (∏ k, ‖c' k‖ ^ L.a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc' k))
    have hterm : ∀ k, Real.log ‖q k z‖ +
        Real.log ‖R.lift x y ⟨k, p k⟩ / R.lift x' y ⟨k, p k⟩‖ = Real.log ‖c' k‖ := by
      intro k
      have hqz : q k z = c' k / (R.lift x y ⟨k, p k⟩ / R.lift x' y ⟨k, p k⟩) := by
        simp only [q]
        rw [hcz, mul_div_assoc, div_self (hzW.2 k).1, mul_one]
      rw [hqz, norm_div, Real.log_div (norm_ne_zero_iff.mpr (hc' k))
        (norm_ne_zero_iff.mpr (hr k))]
      ring
    show Real.log (L.h (R.lift x z)) - Real.log (L.h (R.lift x' z)) = (G z).re
    rw [hcz, L.smul c' _ hc', Real.log_mul hprod hpos.ne', add_sub_cancel_right,
      Real.log_prod fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc' k))]
    simp only [G, Complex.re_sum, Complex.re_ofReal_mul, Complex.add_re, Complex.log_re,
      Complex.ofReal_re]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hterm k, Real.log_zpow]

end GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge
