import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageConnectedComponentRationalPointFieldExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preimage_connectedComponent_rationalPoint_fieldExt : ∀ (k k' : Type) [Field k] [Field k'] (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of k')) (p : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k)) (q : X' ⟶ X) (e : Spec (CommRingCat.of k) ⟶ X) (e' : Spec (CommRingCat.of k') ⟶ X'), Smooth f → IsPullback q f' f p → e ≫ f = 𝟙 _ → e' ≫ f' = 𝟙 _ → e' ≫ q = p ≫ e → q ⁻¹' connectedComponent (e (IsLocalRing.closedPoint k)) = connectedComponent (e' (IsLocalRing.closedPoint k')) := by
  first | exact @GlobalTheory.preimage_connectedComponent_rationalPoint_baseChange | exact GlobalTheory.preimage_connectedComponent_rationalPoint_baseChange | (intros; apply GlobalTheory.preimage_connectedComponent_rationalPoint_baseChange <;> assumption)
