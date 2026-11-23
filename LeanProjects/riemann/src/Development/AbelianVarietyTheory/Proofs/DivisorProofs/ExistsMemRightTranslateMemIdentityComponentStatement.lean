import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemRightTranslateMemIdentityComponent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_rightTranslate_mem_identityComponent : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G], Smooth G.hom → ∀ (U : G.left.Opens) (y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G), (η[G]).left (IsLocalRing.closedPoint k) ∈ U → y.left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) → ∃ z : G.left, z ∈ U ∧ (𝟙 G * (toUnit G ≫ y) : G ⟶ G).left z ∈ U := by
  first | exact @GlobalTheory.exists_mem_and_rightTranslate_mem_of_mem_identityComponent | exact GlobalTheory.exists_mem_and_rightTranslate_mem_of_mem_identityComponent | (intros; apply GlobalTheory.exists_mem_and_rightTranslate_mem_of_mem_identityComponent <;> assumption)
