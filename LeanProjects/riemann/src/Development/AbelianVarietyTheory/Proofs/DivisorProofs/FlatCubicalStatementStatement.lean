import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatCubicalStatement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_cubical_statement : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.FlatCubical := by
  first | exact @GlobalTheory.FlatCubicalProof.flatCubical | exact GlobalTheory.FlatCubicalProof.flatCubical | (intros; apply GlobalTheory.FlatCubicalProof.flatCubical <;> assumption)
