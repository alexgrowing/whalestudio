import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankTensorResidueDegree
import Mathlib
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_tensor_residue_degree : ∀ {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) (T : Scheme.Pullback.Triplet f g), @Module.finrank (X.residueField T.x) T.tensor _ _ T.tensorInl.hom.toModule = g.residueDegree T.y := by
  first | exact @GlobalTheory.ResidueTensorRank.finrank_tensorInl | exact GlobalTheory.ResidueTensorRank.finrank_tensorInl | (intros; apply GlobalTheory.ResidueTensorRank.finrank_tensorInl <;> assumption)
