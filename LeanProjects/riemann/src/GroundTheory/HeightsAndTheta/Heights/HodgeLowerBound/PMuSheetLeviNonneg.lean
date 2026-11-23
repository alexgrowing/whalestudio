import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsSheetChartHolo
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsRefAlongSheet
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open GroundTheory.Heights₂.Heights.Regular (RegChartData)
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.A (coordDiv)
open ReciprocityTheory.AnForm.M (FinHolAtlas)

theorem analyticAt_pi_of_eventually_differentiableAt {d m : ℕ} {f : (Fin d → ℂ) → Fin m → ℂ} {y : Fin d → ℂ}
    (h : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ f y') : AnalyticAt ℂ f y := by
  obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.1 h
  refine AnalyticAt.pi fun i => ReciprocityTheory.AnForm.Osgood.osgood d U (fun w => f w i) hUo (fun z hz => ?_) y hyU
  exact (differentiableAt_pi.mp (hU z hz) i).differentiableWithinAt

theorem RegChartData.contDiffAt_u {n : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas n X}
    (R : RegChartData A) (j : Fin R.N) {ξ : Fin n → ℂ} (hξ : ξ ∈ (R.chart j).target \ coordDiv (R.S j)) :
    ContDiffAt ℝ 2 (R.u j) ξ := by
  have hp : (R.chart j).symm ξ ∈ (R.chart j).source := (R.chart j).map_target hξ.1
  have hYo : R.Yo ∈ 𝓝 ((R.chart j).symm ξ) := by
    refine Filter.mem_of_superset (((R.chart j).isOpen_inter_preimage
      (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed (R.S j)).isOpen_compl).mem_nhds ⟨hp, ?_⟩)
      fun x hx => (R.mem_Yo j x hx.1).2 hx.2
    change (R.chart j) ((R.chart j).symm ξ) ∉ coordDiv (R.S j)
    rw [(R.chart j).right_inv hξ.1]
    exact hξ.2
  obtain ⟨i, hi⟩ := A.cover ((R.chart j).symm ξ)
  have hti : (A.chart i) ((R.chart j).symm ξ) ∈ (A.chart i).target := (A.chart i).map_source hi
  have h1 : ContDiffAt ℝ 2 (R.ph ∘ (A.chart i).symm) ((A.chart i) ((R.chart j).symm ξ)) := by
    refine ((R.ph_smooth i).contDiffAt (Filter.inter_mem ((A.chart i).open_target.mem_nhds hti) ?_)).of_le
      (by first | simp | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤) | exact WithTop.coe_le_coe.mpr le_top)
    refine (A.chart i).continuousAt_symm hti |>.preimage_mem_nhds ?_
    rw [(A.chart i).left_inv hi]
    exact hYo
  have hτ : AnalyticAt ℂ ((A.chart i) ∘ (R.chart j).symm) ξ := ((R.compat j i).2) ξ ⟨hξ.1, hi⟩
  have h2 : ContDiffAt ℝ 2 (fun ξ' => R.ph ((R.chart j).symm ξ')) ξ := by
    refine (h1.comp ξ hτ.restrictScalars.contDiffAt).congr_of_eventuallyEq ?_
    filter_upwards [(R.chart j).continuousAt_symm hξ.1 |>.preimage_mem_nhds
      ((A.chart i).open_source.mem_nhds hi)] with ξ' h
    simp only [Function.comp_apply, (A.chart i).left_inv h]
  have hq : ContDiffAt ℝ 2 (R.q j) ξ :=
    ((R.q_smooth j).contDiffAt ((R.chart j).open_target.mem_nhds hξ.1)).of_le (by first | simp | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤) | exact WithTop.coe_le_coe.mpr le_top)
  exact hq.add h2

theorem LogLogRegularisationSetting.log_h_eq {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)}
    {n : ℕ} {M : CxModel P n} {Xo : Set ((Σ k, ι k) → ℂ)} {A : HermLine ι} (S : LogLogRegularisationSetting M Xo A)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) (hY : M.proj z ∈ S.R.Yo) :
    Real.log (A.h z) = S.R.ph (M.proj z) + Real.log (S.ref.h z) := by
  obtain ⟨z', ⟨hz'o, hz'⟩, hp⟩ := S.Yo_sub _ hY
  obtain ⟨c, hc, rfl⟩ := (M.fibre z' hz' _ hz).1 hp
  have hph := S.ph_eq z' ⟨hz'o, hz'⟩ (by rw [hp]; exact hY)
  have hA : A.h (torusSmul c z') = (∏ k, ‖c k‖ ^ A.a k) * A.h z' := A.smul c z' hc
  have hR : S.ref.h (torusSmul c z') = (∏ k, ‖c k‖ ^ A.a k) * S.ref.h z' := by
    rw [← S.ref_deg]; exact S.ref.smul c z' hc
  have hpos : 0 < ∏ k, ‖c k‖ ^ A.a k := Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hc k)) _
  rw [hA, hR, Real.log_mul hpos.ne' (A.pos z' hz'.1).ne', Real.log_mul hpos.ne' (S.ref.pos z' hz'.1).ne', ← hp,
    hph]
  ring

theorem MuSheetLeviNonneg.proof (hH : SheetChartHolo.Statement) (hR : RefAlongSheet.Statement) :
    MuSheetLeviNonneg.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X Q _
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

end GroundTheory.Heights₂.Heights.LowerBoundFree
