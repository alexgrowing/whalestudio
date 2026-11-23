import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointPullbackResidueField
import Mathlib
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_point_pullback_residue_field : (∀ (R : CommRingCat.{0}) (q : Spec R), (∀ q' : Spec R, q' = q) → IsField ((Spec R).presheaf.stalk q) → IsField R) → ∀ {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) [IsIntegral (Limits.pullback f g)], IsPreimmersion (Scheme.Pullback.Triplet.ofPoint (genericPoint (Limits.pullback f g : Scheme.{0}))).SpecTensorTo → g.residueDegree (Limits.pullback.snd f g (genericPoint (Limits.pullback f g : Scheme.{0}))) ≠ 0 → IsField (Scheme.Pullback.Triplet.ofPoint (genericPoint (Limits.pullback f g : Scheme.{0}))).tensor := by
  first | exact @GlobalTheory.PullbackGenericTensor.isField_tensor | exact GlobalTheory.PullbackGenericTensor.isField_tensor | (intros; apply GlobalTheory.PullbackGenericTensor.isField_tensor <;> assumption)
