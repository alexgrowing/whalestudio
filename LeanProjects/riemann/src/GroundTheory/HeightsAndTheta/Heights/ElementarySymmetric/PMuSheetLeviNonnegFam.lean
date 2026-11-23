import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StMuSheetLeviNonnegFam
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuSheetLeviNonneg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology
open GroundTheory.Heights₂.Heights.Regular (RegChartData)
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.A (coordDiv)

theorem MuSheetLeviNonnegFam.proof (hH : SheetChartHolo.Statement) (hR : RefAlongSheet.Statement) :
    MuSheetLeviNonnegFam.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D X Q _
  filter_upwards [hH K ι (mCoordIdeal D.y) D.n X.M X.S.R Q] with y hy w γ hγ
  obtain ⟨j, hsrc, hYo, hev⟩ := hy w γ hγ
  have hγev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ γ y' ∈ mcPts (mCoordIdeal D.y) :=
    hγ.2.mono fun _ h => ⟨h.1, h.2.1⟩
  obtain ⟨G, hG, hGeq⟩ := hR K ι _ D.n X.M D.Xo (muLine X.H) X.S γ y j hγev hsrc hev
  set g : (Fin D.n → ℂ) → Fin D.n → ℂ := fun y'' => X.S.R.chart j (X.M.proj (γ y'')) with hgdef
  have hg : AnalyticAt ℂ g y := analyticAt_pi_of_eventually_differentiableAt (hev.mono fun _ h => h.2)
  have hgy : g y ∈ (X.S.R.chart j).target \ coordDiv (X.S.R.S j) :=
    ⟨(X.S.R.chart j).map_source hsrc, (X.S.R.mem_Yo j _ hsrc).1 hYo⟩
  have hUo : IsOpen ((X.S.R.chart j).target \ coordDiv (X.S.R.S j)) :=
    (X.S.R.chart j).open_target.sdiff (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed _)
  have hC2 : ContDiffOn ℝ 2 (X.S.R.u j) ((X.S.R.chart j).target \ coordDiv (X.S.R.S j)) :=
    fun ξ hξ => (RegChartData.contDiffAt_u X.S.R j hξ).contDiffWithinAt
  have hL := ((ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm _ _ _ hUo hC2).1 (X.S.R.u_psh j)).2
  have hgU : ∀ᶠ y' in 𝓝 y, g y' ∈ (X.S.R.chart j).target \ coordDiv (X.S.R.S j) :=
    hg.continuousAt.preimage_mem_nhds (hUo.mem_nhds hgy)
  have heq : (fun y' => phMu X.H (γ y')) =ᶠ[𝓝 y] fun y' => (X.S.R.u j ∘ g) y' + 1 * (G y').re := by
    filter_upwards [hγev, hev, hgU, hGeq] with y' h1 h2 h3 h4
    have hY' : X.M.proj (γ y') ∈ X.S.R.Yo := (X.S.R.mem_Yo j _ h2.1).2 h3.2
    have hl := X.S.log_h_eq h1.2 hY'
    show Real.log ((muLine X.H).h (γ y')) =
      X.S.R.q j (g y') + X.S.R.ph ((X.S.R.chart j).symm (g y')) + 1 * (G y').re
    rw [hl, h4, hgdef]
    simp only [(X.S.R.chart j).left_inv h2.1]
    ring
  have hu2 : ContDiffAt ℝ 2 (X.S.R.u j) (g y) := RegChartData.contDiffAt_u X.S.R j hgy
  have hcomp : ContDiffAt ℝ 2 (X.S.R.u j ∘ g) y := hu2.comp y hg.restrictScalars.contDiffAt
  have hre : ContDiffAt ℝ 2 (fun y' => (G y').re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y hG.restrictScalars.contDiffAt
  refine ⟨(hcomp.add (contDiffAt_const.mul hre)).congr_of_eventuallyEq heq, fun v => ?_⟩
  change 0 ≤ levi (fun y' => phMu X.H (γ y')) y v
  rw [ReciprocityTheory.AnForm.levi_congr heq, ReciprocityTheory.AnForm.levi_add_smul 1 hcomp hre,
    ReciprocityTheory.AnForm.levi_re_analytic hG, ReciprocityTheory.AnForm.levi_comp v hg hu2]
  simpa using hL _ hgy _

end GroundTheory.Heights₂.Heights.NineStatements
