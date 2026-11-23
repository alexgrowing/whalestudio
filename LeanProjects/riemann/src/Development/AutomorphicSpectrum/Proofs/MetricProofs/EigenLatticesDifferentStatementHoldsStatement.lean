import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EigenLatticesDifferentStatementHolds
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.EigenLatDifferent
open NumberField GroundTheory.Heights₂.Heights.NineStatements
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_lattices_different_statement_holds : GroundTheory.Heights₂.Heights.NineStatements.EigenLatDifferent.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.EigLat.eigenLat_eq_diffLat | exact GlobalTheory.CompanionTheory.Ar.EigLat.eigenLat_eq_diffLat | (intros; apply GlobalTheory.CompanionTheory.Ar.EigLat.eigenLat_eq_diffLat <;> assumption)
