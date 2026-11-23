import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixDens

theorem chernMat_isForm : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (B : LB X) (φ : Weight p σ B), φ.IsCInf → IsForm fun (c : AlgChart p σ D) y => chernMat φ c y := by
  intro k _ X p σ D B φ hφ
  refine ⟨fun c c' y hy hy' => ?_, fun c => ?_, fun c y hy => ?_⟩
  · have ho := ChartGlue.isOpen_over c.e c'.e.open_source
    have hm := ChartGlue.mem_over c.e hy hy'
    have e : (fun v => (φ.φ (pick φ.isLB y) (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)]
        (fun v => (φ.φ (pick φ.isLB y) (c'.e.symm v) : ℂ)) ∘ c'.e ∘ c.e.symm :=
      eventually_of_mem (ho.mem_nhds hm) fun v hv => by
        simp only [Function.comp_apply, c'.e.left_inv hv.2]
    have e₂ : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hy)
    unfold chernMat AlgChart.hess
    beta_reduce
    rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e,
      ReciprocityTheory.L2DbarEstimates.Y.cmpa_cHess_comp ho hm (c.holo_trans c') (e₂ ▸
        Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hφ.contDiffAt c' hy' (mem_pick _ y))), e₂, chg]
    have hJ : (Matrix.of fun l j => (fderiv ℂ (c'.e ∘ c.e.symm) (c.e y) (ReciprocityTheory.L2DbarEstimates.bas D j)) l) =
        transMat c c' y := rfl
    rw [hJ]
    congr 1
  · intro v hv
    have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U (pick φ.isLB (c.e.symm v))))
    have hm : v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U (pick φ.isLB (c.e.symm v))) :=
      ⟨hv, mem_pick φ.isLB _⟩
    have hs : ContDiffOn ℝ ∞ (fun w => ((φ.φ (pick φ.isLB (c.e.symm v)) (c.e.symm w) : ℝ) : ℂ))
        (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U (pick φ.isLB (c.e.symm v)))) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_chart (hφ _) c)
    have hc : ContinuousAt
        (fun w => cHess D (fun w => ((φ.φ (pick φ.isLB (c.e.symm v)) (c.e.symm w) : ℝ) : ℂ)) w) v :=
      continuousAt_pi.2 fun a => continuousAt_pi.2 fun b =>
        (ReciprocityTheory.L2DbarEstimates.Y.continuousOn_wd_wdb ho hs a b).continuousAt (ho.mem_nhds hm)
    refine ContinuousAt.continuousWithinAt (hc.congr ?_)
    filter_upwards [ho.mem_nhds hm] with w hw
    unfold chernMat
    beta_reduce
    rw [c.hess_eq hφ (c.e.map_target hw.1) hw.2 (mem_pick _ _), AlgChart.hess, c.e.right_inv hw.1]
  · have hd := hφ.contDiffAt c hy (mem_pick φ.isLB y)
    set g : V D → ℂ := fun v => ((φ.φ (pick φ.isLB y) (c.e.symm v) : ℝ) : ℂ) with hg
    have hg2 : ContDiffAt ℝ 2 g (c.e y) := Complex.ofRealCLM.contDiff.contDiffAt.comp _ hd
    have hgc : (fun w => (starRingEnd ℂ) (g w)) = g := funext fun w => by simp [g]
    show (cHess D g (c.e y)).IsHermitian
    ext j l
    simp only [Matrix.conjTranspose_apply, cHess, Matrix.of_apply]
    show (starRingEnd ℂ) (ReciprocityTheory.L2DbarEstimates.wd D l (ReciprocityTheory.L2DbarEstimates.wdb D j g) (c.e y)) =
      ReciprocityTheory.L2DbarEstimates.wd D j (ReciprocityTheory.L2DbarEstimates.wdb D l g) (c.e y)
    have h1 : (fun w => (starRingEnd ℂ) (ReciprocityTheory.L2DbarEstimates.wdb D j g w)) = ReciprocityTheory.L2DbarEstimates.wd D j g := by
      funext w
      rw [← ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.wd_conj' D j g w, hgc]
    rw [← ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.wdb_conj' D l (ReciprocityTheory.L2DbarEstimates.wdb D j g) (c.e y), h1,
      ReciprocityTheory.L2DbarEstimates.comm_wd_wdb g (c.e y) hg2 j l]

end GlobalTheory.MixDens
