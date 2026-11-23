import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSpecFiniteFreeOfFiniteFlat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbRep
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_spec_finite_free_of_finite_flat : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z → LocallyOfFinitePresentation z → ∀ s : S, ∃ (W : S.Opens) (A B : Type) (_ : CommRing A) (_ : CommRing B) (_ : Algebra A B) (_ : Module.Free A B) (_ : Module.Finite A B) (eW : W.toScheme ≅ Spec (CommRingCat.of A)) (eZ : (z ⁻¹ᵁ W).toScheme ≅ Spec (CommRingCat.of B)), s ∈ W ∧ eZ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = (z ∣_ W) ≫ eW.hom := by
  first | exact @GlobalTheory.FiniteFlatLocal.exists_finFree_local | exact GlobalTheory.FiniteFlatLocal.exists_finFree_local | (intros; apply GlobalTheory.FiniteFlatLocal.exists_finFree_local <;> assumption)
