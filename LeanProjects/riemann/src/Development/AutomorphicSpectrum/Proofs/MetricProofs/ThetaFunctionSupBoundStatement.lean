import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaFunctionSupBound
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_function_sup_bound : ∀ {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ} (a : ArchFrame P z g), (∀ l l' : a.u.Λ, ∃ k : ℤ, (a.herm l l').im = k) → (∀ w : Fin g → ℂ, (∀ l : a.u.Λ, ∃ k : ℤ, (a.herm w l).im = k) → w ∈ a.u.Λ) → (∀ l l' : a.u.Λ, a.χ (l + l') = a.χ l * a.χ l' * Complex.exp (Real.pi * Complex.I * (a.herm l l').im)) → ∀ (m : ℕ) (θ : (Fin g → ℂ) → ℂ) (Ix : Type) [Fintype Ix] (r : Ix → Fin g → ℂ) (f : Ix → (Fin g → ℂ) → ℂ), 1 ≤ m → a.IsTheta 1 θ → θ ≠ 0 → (∀ w : Fin g → ℂ, (m : ℂ) • w ∈ a.u.Λ → ∃ i, w - r i ∈ a.u.Λ) → (∀ i, (m : ℂ) • r i ∈ a.u.Λ) → (∀ i, a.IsTheta (m ^ 2) (f i)) → (∀ i (w : Fin g → ℂ) (N : ℕ), 1 ≤ N → (N : ℂ) • w ∈ a.u.Λ → a.nrm (m ^ 2) (f i) w = a.nrm 1 θ (r i + (m : ℂ) • w)) → (∀ i w, a.nrm (m ^ 2) (f i) w = a.nrm 1 θ (r i + (m : ℂ) • w)) ∧ ∀ F, a.IsTheta (m ^ 2) F → ∃ c : Ix → ℂ, F = ∑ i, c i • f i := by
  first | exact @GlobalTheory.CompanionTheory.ThetaSpan.theta_span | exact GlobalTheory.CompanionTheory.ThetaSpan.theta_span | (intros; apply GlobalTheory.CompanionTheory.ThetaSpan.theta_span <;> assumption)
