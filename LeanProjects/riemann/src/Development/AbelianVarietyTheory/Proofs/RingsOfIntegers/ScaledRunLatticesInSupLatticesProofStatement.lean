import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ScaledRunLatticesInSupLatticesProof
import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledRunLattices_in_supLattices : ScaledLatticesInSupLattices := by
  first | exact @GlobalTheory.PlaceTop.scaledRunLatticesInSupLattices_proof | exact GlobalTheory.PlaceTop.scaledRunLatticesInSupLattices_proof | (intros; apply GlobalTheory.PlaceTop.scaledRunLatticesInSupLattices_proof <;> assumption)
