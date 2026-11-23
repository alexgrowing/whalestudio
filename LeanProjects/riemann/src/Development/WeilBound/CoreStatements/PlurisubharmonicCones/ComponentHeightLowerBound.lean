import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionComparisonStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section
namespace LevelTowerAlt

theorem ph_usc {n : ℕ} {X : Type} [TopologicalSpace X] {A : ReciprocityTheory.AnForm.M.FinHolAtlas n X}
    (B : GroundTheory.Heights₂.Heights.Regular.BoundedPshData A) (x : X) (r : ℝ) (hr : B.ph x < r) :
    ∀ᶠ x' in 𝓝 x, B.ph x' < r := by
  obtain ⟨j, hj⟩ := B.cover x
  have hs : x ∈ (B.chart j).source :=
    B.toPotentialCharts.mid_subset_source j (B.toPotentialCharts.inner_subset_mid j hj)
  have ht := (B.chart j).map_source hs
  have hn : (B.chart j).target ∈ 𝓝 (B.chart j x) := (B.chart j).open_target.mem_nhds ht
  have h1 : ∀ᶠ y in 𝓝[(B.chart j).target] (B.chart j x),
      B.q j y + B.ph ((B.chart j).symm y) < B.q j (B.chart j x) + B.ph x + (r - B.ph x) / 2 :=
    (B.u_psh j).1 _ ht _ (by
      show B.q j (B.chart j x) + B.ph ((B.chart j).symm (B.chart j x)) < _
      rw [(B.chart j).left_inv hs]; linarith)
  rw [nhdsWithin_eq_nhds.2 hn] at h1
  have h2 : ∀ᶠ y in 𝓝 (B.chart j x), B.q j (B.chart j x) - (r - B.ph x) / 2 < B.q j y :=
    ((B.q_smooth j).continuousOn.continuousAt hn).eventually (lt_mem_nhds (by linarith))
  have hc := (B.chart j).continuousAt hs
  filter_upwards [hc.eventually h1, hc.eventually h2, (B.chart j).open_source.mem_nhds hs] with y a b c
  rw [(B.chart j).left_inv c] at a
  linarith

theorem Xo_dense {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type}
    [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
    (D : ComponentData II Ψ K J Ω W) {w : (Σ k, J k) → ℂ} (hw : w ∈ mcPts (mCoordIdeal D.y)) :
    (𝓝[D.Xo] w).NeBot := by
  classical
  obtain ⟨a, t, ht, c, hc, rfl⟩ := D.chart_cover w hw
  have ht1 : t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1 :=
    mem_ball_zero_iff.2 (by linarith)
  let e : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ := fun i => if t i = 0 then 1 else 0
  have h0 : Tendsto (fun s : ℝ => t + (s : ℂ) • e) (𝓝[>] 0) (𝓝 t) := by
    have : Continuous fun s : ℝ => t + (s : ℂ) • e := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hγ := ((D.chart a).analytic t ht1).continuousAt
  have hT : Continuous fun z : (Σ k, J k) → ℂ => torusSmul c z := by
    unfold torusSmul; fun_prop
  have h1 : Tendsto (fun s : ℝ => torusSmul c ((D.chart a).γ (t + (s : ℂ) • e))) (𝓝[>] 0)
      (𝓝[D.Xo] (torusSmul c ((D.chart a).γ t))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨(hT.tendsto _).comp (hγ.tendsto.comp h0), ?_⟩
    filter_upwards [h0.eventually (Metric.isOpen_ball.mem_nhds ht1), self_mem_nhdsWithin] with s hs hs0
    have hm := (D.chart a).mem _ hs
    refine ⟨mcPts_smul D.arith.2.1.2.1 c hc hm, fun hb => ?_⟩
    have hb' := D.bd_torus _ hb (fun k => (c k)⁻¹) fun k => inv_ne_zero (hc k)
    have he : torusSmul (fun k => (c k)⁻¹) (torusSmul c ((D.chart a).γ (t + (s : ℂ) • e))) =
        (D.chart a).γ (t + (s : ℂ) • e) := by
      funext p
      simp [torusSmul, hc]
    rw [he, (D.chart a).boundary _ hs] at hb'
    obtain ⟨i, -, hi⟩ := hb'
    have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hs0)
    by_cases h : t i = 0 <;> simp [e, h, hs'] at hi
  exact h1.neBot

end LevelTowerAlt
