import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecTensorPreimmersion
import Mathlib
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_tensor_preimmersion : ∀ {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) (T : Scheme.Pullback.Triplet f g), IsPreimmersion T.SpecTensorTo := by
  first | exact @GlobalTheory.isPreimmersion_SpecTensorTo | exact GlobalTheory.isPreimmersion_SpecTensorTo | (intros; apply GlobalTheory.isPreimmersion_SpecTensorTo <;> assumption)
