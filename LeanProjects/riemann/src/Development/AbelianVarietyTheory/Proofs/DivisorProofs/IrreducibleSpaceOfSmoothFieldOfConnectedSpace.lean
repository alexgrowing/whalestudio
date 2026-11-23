import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct in
open scoped CategoryTheory.Obj in

theorem _root_.GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)), Smooth f →
      ConnectedSpace X → IrreducibleSpace X := by
  intro k _ X f hf hc
  haveI := _root_.GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace f
  infer_instance

end GlobalTheory
