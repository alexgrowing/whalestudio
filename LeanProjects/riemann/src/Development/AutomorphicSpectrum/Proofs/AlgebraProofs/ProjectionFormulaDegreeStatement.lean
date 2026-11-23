import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjectionFormulaDegree
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projection_formula_degree : GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaDegree.Statement.{0} := by
  first | exact @GlobalTheory.CompanionTheory.FieldNumbers.projectionFormulaDegree | exact GlobalTheory.CompanionTheory.FieldNumbers.projectionFormulaDegree | (intros; apply GlobalTheory.CompanionTheory.FieldNumbers.projectionFormulaDegree <;> assumption)
