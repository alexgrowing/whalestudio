import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenConnectedComponentOfIsLocallyNoetherian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_connectedComponent_of_isLocallyNoetherian' : ∀ (X : Scheme.{0}), IsLocallyNoetherian X → ∀ x : X, IsOpen (connectedComponent x) := by
  first | exact @GlobalTheory.isOpen_connectedComponent_of_isLocallyNoetherian | exact GlobalTheory.isOpen_connectedComponent_of_isLocallyNoetherian | (intros; apply GlobalTheory.isOpen_connectedComponent_of_isLocallyNoetherian <;> assumption)
