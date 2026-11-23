import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SquareSystemPolarVanishing
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_system_polar_vanishing : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (P : Ideal (MRing ι)) (Re : Realis SY P) (a₀ : σ) (ε : σ → ℤ) (Q : SqSys Re a₀ ε) (n : σ → ℤ), n a₀ = 0 → ∀ t, 0 < t → t ≤ Q.an.SW.t₀ → polar (d + 2) (Re.num II t) (fun _ a => (n a : ℝ)) = 0 ∧ ∀ k : ℕ, 1 ≤ k → 2 * k ≤ d + 2 → polar (d + 2) (Re.num II t) (mix (2 * k) (fun a => (ε a : ℝ)) fun a => (n a : ℝ)) = -∑ i ∈ Finset.range k, polar (d + 2) (fun w => mInt Q.an.SW.A (fun r => Q.an.SW.potT (w r) t) (Q.an.gT t)) (Q.an.wcoef (fun a => (n a : ℝ)) k i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.first_half_at_scale | exact GlobalTheory.CompanionTheory.Ar.PB.first_half_at_scale | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.first_half_at_scale <;> assumption)
