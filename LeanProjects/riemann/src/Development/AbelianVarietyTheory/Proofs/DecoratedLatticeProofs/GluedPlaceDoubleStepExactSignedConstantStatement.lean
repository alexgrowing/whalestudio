import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedPlaceDoubleStepExactSignedConstant
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleUnif
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedPlace_doubleStep_exact_signed_constant : ∀ D : D7, GlobalTheory.FinPl.VertexExact D := by
  first | exact @GlobalTheory.FinPl.VertexExactCount.vertexExact | exact GlobalTheory.FinPl.VertexExactCount.vertexExact | (intros; apply GlobalTheory.FinPl.VertexExactCount.vertexExact <;> assumption)
