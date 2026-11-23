import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointHTOfFarguesHodgeTate
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointHT_of_fargues_hodge_tate : FarguesHodgeTate → PointHT := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.Fargues.pointHT | exact GlobalTheory.CompanionTheory.Ar.HT.Fargues.pointHT | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.Fargues.pointHT <;> assumption)
