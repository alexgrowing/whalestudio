import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxE

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder ContDiff

namespace GlobalTheory.CurveDens

theorem cHess_apply_eq_ddbar {n : ℕ} {g : ReciprocityTheory.L2DbarEstimates.V n → ℂ} {x : ReciprocityTheory.L2DbarEstimates.V n}
    (hg : ContDiffAt ℝ 2 g x) (j k : Fin n) :
    ReciprocityTheory.L2DbarEstimates.cHess n g x j k =
      ddbar g x (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) := by
  have e : ReciprocityTheory.L2DbarEstimates.wdb n k g = fun y => dbar g y (EuclideanSpace.single k 1) := by
    funext y
    simp only [ReciprocityTheory.L2DbarEstimates.wdb, dbar_apply, ReciprocityTheory.L2DbarEstimates.bas, smul_eq_mul]
    ring
  rw [ddbar_eq_del_dbar hg, del_apply, ReciprocityTheory.L2DbarEstimates.cHess, Matrix.of_apply, e]
  simp only [ReciprocityTheory.L2DbarEstimates.wd, ReciprocityTheory.L2DbarEstimates.bas, smul_eq_mul]
  ring

end GlobalTheory.CurveDens

namespace GlobalTheory.CurveDens

theorem chernDens_curve : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ),
    (∀ (B : LB X) (φ : Weight p σ B), φ.IsCInf → IsDens fun (c : AlgChart p σ 1) y => c.chernDens φ y) ∧
    ∀ (L : X.Modules) (g : Met p σ L 1), g.IsCInf → ∀ (U : X.Opens) (t : Γ(L, U)),
      IsFrame (fun _ : Fin 1 => t) → ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∈ ptsIn p σ U →
        c.chernDens g.detWeight y = -(leviForm (fun v => Real.log (g.form t t (c.e.symm v)).re) (c.e y)
          (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)).re / Real.pi := by
  intro k _ X p σ
  refine ⟨fun B φ hφ => ⟨fun c c' y hy hy' => c.chernDens_trans c' hφ hy hy', fun c v hv => ?_⟩, ?_⟩
  · have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U (pick φ.isLB (c.e.symm v))))
    have hm : v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U (pick φ.isLB (c.e.symm v))) :=
      ⟨hv, mem_pick φ.isLB _⟩
    have hs : ContDiffOn ℝ ∞ (fun w => ((φ.φ (pick φ.isLB (c.e.symm v)) (c.e.symm w) : ℝ) : ℂ))
        (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U (pick φ.isLB (c.e.symm v)))) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_chart (hφ _) c)
    have hc := ReciprocityTheory.L2DbarEstimates.Y.continuousOn_wd_wdb ho hs 0 0
    refine ContinuousAt.continuousWithinAt ?_
    refine ((continuous_const.mul Complex.continuous_re).continuousAt.comp
      (hc.continuousAt (ho.mem_nhds hm)) (f := fun w => ReciprocityTheory.L2DbarEstimates.wd 1 0 (ReciprocityTheory.L2DbarEstimates.wdb 1 0 _) w)
      (g := fun z : ℂ => (Nat.factorial 1 : ℝ) / Real.pi ^ 1 * z.re)).congr ?_
    filter_upwards [ho.mem_nhds hm] with w hw
    rw [Function.comp_apply, c.chernDens_eq hφ (c.e.map_target hw.1) hw.2, AlgChart.hess,
      c.e.right_inv hw.1, Matrix.det_unique]
    rfl
  · intro L g hg U t ht c y hy hU
    let c₀ : VB.Chart L 1 := ⟨U, fun _ => t, ht⟩
    have hi : y ∈ ptsIn p σ ((det L 1).U c₀) := hU
    rw [c.chernDens_eq hg.detWeight hy hi]
    simp only [AlgChart.hess, Matrix.det_unique]
    have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) U)
    have hm := ChartGlue.mem_over c.e hy hU
    have e : (fun v => ((g.detWeight.φ c₀ (c.e.symm v) : ℝ) : ℂ)) =ᶠ[𝓝 (c.e y)]
        fun v => -((Real.log (g.form t t (c.e.symm v)).re : ℝ) : ℂ) := by
      filter_upwards [ho.mem_nhds hm] with v hv
      rw [← Complex.ofReal_neg]
      congr 1
      show -Real.log (g.G c₀ (c.e.symm v)).det.re = -Real.log (g.form t t (c.e.symm v)).re
      rw [Matrix.det_unique, ← g.form_frame c₀ hv.2]
    have hd : ContDiffAt ℝ 2 (fun v => g.detWeight.φ c₀ (c.e.symm v)) (c.e y) :=
      hg.detWeight.contDiffAt c hy hi
    have hu := (contDiffAt_ofReal_comp hd).congr_of_eventuallyEq e.symm
    rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e, cHess_apply_eq_ddbar hu]
    erw [ddbar_neg]
    simp only [leviForm, Nat.factorial_one, Nat.cast_one, pow_one, Fin.default_eq_zero]
    simp only [ContinuousLinearMap.neg_apply, Complex.neg_re]
    ring

end GlobalTheory.CurveDens
