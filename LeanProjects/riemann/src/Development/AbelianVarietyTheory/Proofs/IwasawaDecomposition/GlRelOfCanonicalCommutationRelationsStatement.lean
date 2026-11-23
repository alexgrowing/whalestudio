import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlRelOfCanonicalCommutationRelations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
open Matrix GlobalTheory.Mem.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glRel_of_canonicalCommutationRelations : ∀ (A : Type) [Ring A] (n m : ℕ) (x d : Fin n × Fin m → A), IsCCR x d → Formalism.REAL.GlRel (fun i j : Fin n => ∑ a, x (i, a) * d (j, a)) ∧ Formalism.REAL.GlRel (fun a b : Fin m => -∑ i, x (i, b) * d (i, a)) := by
  first | exact @GlobalTheory.Mem.Lift.glRel_of_isCCR | exact GlobalTheory.Mem.Lift.glRel_of_isCCR | (intros; apply GlobalTheory.Mem.Lift.glRel_of_isCCR <;> assumption)
