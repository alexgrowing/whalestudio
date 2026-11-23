import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaFunctionEvenBound
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_function_even_bound : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ} (a : ArchFrame P z g), 1 ≤ g → (∀ l l' : a.u.Λ, ∃ k : ℤ, (a.herm l l').im = k) → (∀ w : Fin g → ℂ, (∀ l : a.u.Λ, ∃ k : ℤ, (a.herm w l).im = k) → w ∈ a.u.Λ) → (∀ l l' : a.u.Λ, a.χ (l + l') = a.χ l * a.χ l' * Complex.exp (Real.pi * Complex.I * (a.herm l l').im)) → (∀ l : a.u.Λ, a.χ l ^ 2 = 1) → ∀ (θ : (Fin g → ℂ) → ℂ) (b : ℝ), a.IsTheta 1 θ → a.IsThetaMeanSquareNorm θ b → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ √(2 * g) ∧ (∀ w, a.nrm 1 θ w ≤ b * Real.exp (g * Real.log (1 + 1 / ρ) + C₀ * g * Real.log (2 * g))) ∧ ∀ᶠ m : ℕ in Filter.atTop, ∀ (Ix : Type) [Fintype Ix] (r : Ix → Fin g → ℂ), (∀ i, (m : ℂ) • r i ∈ a.u.Λ ∧ θ (r i) ≠ 0) → (∀ w : Fin g → ℂ, (m : ℂ) • w ∈ a.u.Λ → θ w ≠ 0 → ∃! i, w - r i ∈ a.u.Λ) → Nonempty Ix ∧ (Fintype.card Ix : ℝ) * (Real.pi / 96 * (ρ ^ 2)⁻¹ - (g * Real.log (1 + 1 / ρ) + C₀ * g * Real.log (2 * g))) ≤ ∑ i, -Real.log (a.nrm 1 θ (r i) / b) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.NForm.nform | exact GlobalTheory.CompanionTheory.Ar.NForm.nform | (intros; apply GlobalTheory.CompanionTheory.Ar.NForm.nform <;> assumption)
