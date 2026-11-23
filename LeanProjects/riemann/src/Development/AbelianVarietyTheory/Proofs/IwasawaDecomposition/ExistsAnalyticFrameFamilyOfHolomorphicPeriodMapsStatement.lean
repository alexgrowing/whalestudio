import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticFrameFamilyOfHolomorphicPeriodMaps
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtEqOfPtOfFrameEq
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analytic_frame_family_of_holomorphic_periodMaps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (La : Type) [AddCommGroup La] [Module (𝓞 E) La] (φ : La ≃ₗ[𝓞 E] X.Λ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (idx : Fin g → ℕ) (d : ℕ) (B : Set (ReciprocityTheory.L2DbarEstimates.V d)) (P : ReciprocityTheory.L2DbarEstimates.V d → (La →+ (Fin g → ℂ))) (b₀ : ReciprocityTheory.L2DbarEstimates.V d), IsOpen B → b₀ ∈ B → (∀ b ∈ B, ∀ (a : 𝓞 E) (v : La) (j : Fin g), P b (a • v) j = ty j (a : E) * P b v j) → (∀ v, DifferentiableOn ℂ (fun b => P b v) B) → (∀ ρ ∈ X.Ψ, ∀ m < X.p0, ∃ j, ty j = conjEmb ρ ∧ idx j = m) → (∀ j j', ty j = ty j' → idx j = idx j' → j = j') → (∀ j, ty j ∉ X.Ψ → idx j < X.p0) → (∀ b ∈ B, ∃ x' ∈ X.dom, ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ v, P b v = h (fun j => Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j) (idx j))) → ∃ s : ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, AnalyticAt ℂ s b₀ ∧ ∀ᶠ b in 𝓝 b₀, s b ∈ X.dom ∧ ∀ x' ∈ X.dom, (∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ v, P b v = h (fun j => Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j) (idx j))) → (∀ (τ : X.Ψ) (a b' : Fin r), X.p0 ≤ (a : ℕ) → (b' : ℕ) < X.p0 → ((ReciprocityTheory.ChartRestriction.G.FD.mat (s b) τ)⁻¹ * ReciprocityTheory.ChartRestriction.G.FD.mat x' τ) a b' = 0) ∧ (∀ (τ : X.Ψ) (a b' : Fin r), X.p0 ≤ (a : ℕ) → (b' : ℕ) < X.p0 → ((ReciprocityTheory.ChartRestriction.G.FD.mat x' τ)⁻¹ * ReciprocityTheory.ChartRestriction.G.FD.mat (s b) τ) a b' = 0) := by
  first | exact @GlobalTheory.PeriodFamFrame.lift_frame | exact GlobalTheory.PeriodFamFrame.lift_frame | (intros; apply GlobalTheory.PeriodFamFrame.lift_frame <;> assumption)
