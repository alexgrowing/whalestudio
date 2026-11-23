import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BoundaryPolynomialFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveChartHolomorphicRatioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveProjectiveEmbeddingStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical
open scoped LinearAlgebra.Projectivization

namespace GlobalTheory.ProjEmbed

theorem fderiv_mem_span_eq_zero (d M : ℕ) (g : (Fin d → ℂ) → Fin M → ℂ) (z0 : Fin d → ℂ)
    (a0 : Fin M) (Ψ : Fin d → (Fin M → ℂ) → ℂ) (hg : DifferentiableAt ℂ g z0)
    (hΨ : ∀ b, DifferentiableAt ℂ (Ψ b) (g z0)) (he : ∀ b, ∀ᶠ z in 𝓝 z0, z b = Ψ b (g z))
    (h1 : ∀ᶠ z in 𝓝 z0, g z a0 = 1) (v : Fin d → ℂ)
    (hv : fderiv ℂ g z0 v ∈ Submodule.span ℂ {g z0}) : v = 0 := by
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.1 hv
  have hcomp : ∀ w, fderiv ℂ g z0 w a0 = fderiv ℂ (fun z => g z a0) z0 w := fun w => by
    rw [fderiv_pi (fun i => (differentiableAt_pi.1 hg) i)]
    rfl
  have hc0 : fderiv ℂ (fun z => g z a0) z0 = 0 := by
    rw [(show (fun z => g z a0) =ᶠ[𝓝 z0] fun _ => (1 : ℂ) from h1).fderiv_eq]
    exact fderiv_const_apply 1
  have hga : g z0 a0 = 1 := h1.self_of_nhds
  have hμ0 : μ = 0 := by
    have := congrFun hμ a0
    rw [Pi.smul_apply, hga, smul_eq_mul, mul_one, hcomp, hc0] at this
    simpa using this
  have hL : fderiv ℂ g z0 v = 0 := by rw [← hμ, hμ0, zero_smul]
  funext b
  have e1 : fderiv ℂ (fun z : Fin d → ℂ => z b) z0 = fderiv ℂ (fun z => Ψ b (g z)) z0 :=
    (show (fun z : Fin d → ℂ => z b) =ᶠ[𝓝 z0] fun z => Ψ b (g z) from he b).fderiv_eq
  have e2 : fderiv ℂ (fun z : Fin d → ℂ => z b) z0 v = v b := by
    rw [(hasFDerivAt_apply b z0).fderiv]
    rfl
  have e3 : fderiv ℂ (fun z => Ψ b (g z)) z0 v = fderiv ℂ (Ψ b) (g z0) (fderiv ℂ g z0 v) := by
    rw [show (fun z => Ψ b (g z)) = Ψ b ∘ g from rfl, fderiv_comp z0 (hΨ b) hg]
    rfl
  rw [← e2, e1, e3, hL, map_zero]
  rfl

theorem isProjective_finAtlas : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) (R : AnRead p σ d) [CompactSpace (CxPts p σ)], IsProjOver p → IsProjective R.finAtlas := by
  intro k _ X p σ d R _ hP
  obtain ⟨N, i, hci, hi⟩ := hP
  obtain ⟨F, hFi, hFr⟩ := GlobalTheory.T.exists_injective_projective_embedding k X p σ N i hi
  refine ⟨N, F, hFi, fun x => ?_⟩
  have hcov : (⨆ a, i ⁻¹ᵁ GlobalTheory.ProjSpace.chart k N a) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, GlobalTheory.ProjSpace.iSup_chart, Scheme.Hom.preimage_top]
  obtain ⟨a, ha⟩ := exists_mem_ptsIn hcov x
  set W0 := i ⁻¹ᵁ GlobalTheory.ProjSpace.chart k N a with hW0
  set G : CxPts p σ → Fin (N + 1) → ℂ := fun y j => ev p σ W0 (GlobalTheory.ProjSpace.pullRatio i W0 a le_rfl j) y
    with hG
  refine ⟨ptsIn p σ W0, isOpen_ptsIn _, ha, G,
    fun j => (R.finAtlas_holoOn_iff (isOpen_ptsIn _)).2 (R.holoOn_ev _ _), fun y hy => hFr a y hy, ?_⟩
  intro j hx v hv
  obtain ⟨c, hc⟩ := R.isAlgAtlas_finAtlas j
  rw [hc] at hx hv
  have hxs : x ∈ c.e.source := hx
  have hxU : x ∈ ptsIn p σ c.U := c.source_subset hxs
  choose Ψ hΨd hΨe using fun b : Fin d => GlobalTheory.T.projective_chart_holomorphic_ratio k X p σ N i hi a c.U (c.x b) x hxU ha
  have hz0 : c.finChart.symm (c.finChart x) = x := c.finChart.left_inv hx
  have hgx : (G ∘ c.finChart.symm) (c.finChart x) = G x := by simp only [Function.comp_apply, hz0]
  have hmt : c.finChart x ∈ c.finChart.target := c.finChart.map_source hx
  have hsymm : Tendsto c.finChart.symm (𝓝 (c.finChart x)) (𝓝 x) := by
    have := c.finChart.continuousAt_symm hmt
    rwa [ContinuousAt, hz0] at this
  have htg : ∀ᶠ z in 𝓝 (c.finChart x), z ∈ c.finChart.target :=
    c.finChart.open_target.mem_nhds hmt
  have hW : ∀ᶠ z in 𝓝 (c.finChart x), c.finChart.symm z ∈ ptsIn p σ W0 :=
    hsymm.eventually ((isOpen_ptsIn _).mem_nhds ha)
  refine fderiv_mem_span_eq_zero d (N + 1) (G ∘ c.finChart.symm) (c.finChart x) a Ψ ?_ ?_ ?_ ?_ v (hgx ▸ hv)
  · refine differentiableAt_pi.2 fun b => ?_
    have hh := (c.analyticOnNhd_finChart_iff (isOpen_ptsIn W0)
      (ev p σ W0 (GlobalTheory.ProjSpace.pullRatio i W0 a le_rfl b))).2 (c.holo W0 _) (c.finChart x)
      ⟨hmt, by simpa only [Set.mem_preimage, hz0] using ha⟩
    exact hh.differentiableAt
  · intro b
    rw [hgx]
    exact hΨd b
  · intro b
    filter_upwards [htg, hsymm.eventually (hΨe b)] with z hz hz'
    have hzs : c.finChart.symm z ∈ c.e.source := c.finChart.map_target hz
    calc z b = c.finChart (c.finChart.symm z) b := by rw [c.finChart.right_inv hz]
      _ = ev p σ c.U (c.x b) (c.finChart.symm z) := c.finChart_eq_ev hzs b
      _ = _ := hz'
  · filter_upwards [hW] with z hz
    show ev p σ W0 (GlobalTheory.ProjSpace.pullRatio i W0 a le_rfl a) (c.finChart.symm z) = 1
    rw [GlobalTheory.ProjSpace.pullRatio_self, ev_eq hz, map_one]

end GlobalTheory.ProjEmbed
