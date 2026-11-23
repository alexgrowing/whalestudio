import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UniformisedDegreePolynomialAntisymmetric
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_degree_polynomial_antisymmetric : Inputs → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j D : ℕ) (S : AnSys D (Ψ × Fin N)), j ≤ N → D = antisymDegree Ψ N → IsUniformised S.A S.open' j S.potH → ∃ v : ℝ, 0 < v ∧ toWt S.degPoly = C v * antisymDelta Ψ N := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.anSys_proportional | exact GlobalTheory.CompanionTheory.Ar.PB.anSys_proportional | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.anSys_proportional <;> assumption)
