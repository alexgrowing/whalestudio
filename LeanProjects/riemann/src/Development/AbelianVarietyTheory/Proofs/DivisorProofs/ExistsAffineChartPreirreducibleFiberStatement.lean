import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartPreirreducibleFiber
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_chart_preirreducible_fiber' : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X), Smooth f → e ≫ f = 𝟙 _ → ∀ s : S, ∃ (V : S.Opens) (W : X.Opens) (_ : W ≤ f ⁻¹ᵁ V), IsAffineOpen V ∧ IsAffineOpen W ∧ e s ∈ W ∧ ∀ (k : Type) [Field k] (p : Spec (CommRingCat.of k) ⟶ S), p (IsLocalRing.closedPoint k) = s → PreirreducibleSpace ↥(pullback (W.ι ≫ f) p) := by
  first | exact @GlobalTheory.exists_affine_chart_preirreducible_fiber | exact GlobalTheory.exists_affine_chart_preirreducible_fiber | (intros; apply GlobalTheory.exists_affine_chart_preirreducible_fiber <;> assumption)
