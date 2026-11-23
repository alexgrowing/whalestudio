import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaDerivativeBound
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_derivative_bound : ∀ {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ} (a : ArchFrame P z g), (∀ l l' : a.u.Λ, ∃ k : ℤ, (a.herm l l').im = k) → (∀ w : Fin g → ℂ, (∀ l : a.u.Λ, ∃ k : ℤ, (a.herm w l).im = k) → w ∈ a.u.Λ) → (∀ l l' : a.u.Λ, a.χ (l + l') = a.χ l * a.χ l' * Complex.exp (Real.pi * Complex.I * (a.herm l l').im)) → ∀ (θ : (Fin g → ℂ) → ℂ) (v : Fin g → ℂ) (n' i : ℕ), a.IsTheta 1 θ → θ ≠ 0 → v ≠ 0 → i ≤ n' → ∃ F, a.IsTheta (3 * n') F ∧ (∀ k < i, iteratedDeriv k (fun τ : ℂ => F (τ • v)) 0 = 0) ∧ iteratedDeriv i (fun τ : ℂ => F (τ • v)) 0 ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Jump.lefschetz_direction | exact GlobalTheory.CompanionTheory.Ar.Sl.Jump.lefschetz_direction | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Jump.lefschetz_direction <;> assumption)
