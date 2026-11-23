import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveChartHolomorphicRatio
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemRangeAppLEChartIff
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsClosedEmbeddingOfAffine
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsImmersionProjSpaceOfLocalLinearChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points GlobalTheory.CxPts
open scoped LinearAlgebra.Projectivization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_chart_holomorphic_ratio : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (N : ℕ) (i : X ⟶ PSpace k N) [IsClosedImmersion i], i ≫ PSpace.str k N = p → ∀ (a : Fin (N + 1)) (V : X.Opens) (f : Γ(X, V)) (x : CxPts p σ), x ∈ ptsIn p σ V → x ∈ ptsIn p σ (i ⁻¹ᵁ GlobalTheory.ProjSpace.chart k N a) → ∃ Ψ : (Fin (N + 1) → ℂ) → ℂ, DifferentiableAt ℂ Ψ (fun j => ev p σ (i ⁻¹ᵁ GlobalTheory.ProjSpace.chart k N a) (GlobalTheory.ProjSpace.pullRatio i _ a le_rfl j) x) ∧ ∀ᶠ y in 𝓝 x, ev p σ V f y = Ψ (fun j => ev p σ (i ⁻¹ᵁ GlobalTheory.ProjSpace.chart k N a) (GlobalTheory.ProjSpace.pullRatio i _ a le_rfl j) y) := by
  first | exact @GlobalTheory.ProjLoc.exists_holo_pullRatio | exact GlobalTheory.ProjLoc.exists_holo_pullRatio | (intros; apply GlobalTheory.ProjLoc.exists_holo_pullRatio <;> assumption)
