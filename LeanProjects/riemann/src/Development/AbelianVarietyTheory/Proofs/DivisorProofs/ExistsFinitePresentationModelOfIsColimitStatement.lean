import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePresentationModelOfIsColimit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorIff
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finitePresentation_descent_of_isColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (D : Type) [CommRing D] [Algebra c.pt D], Algebra.FinitePresentation c.pt D →
    ∃ (j : J) (A : Type) (_ : CommRing A) (_ : Algebra (F.obj j) A)
      (_ : Algebra.FinitePresentation (F.obj j) A),
      letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Nonempty (c.pt ⊗[F.obj j] A ≃ₐ[c.pt] D) := by
  first | (exact @GlobalTheory.FpDescent.exists_finitePresentation_model_of_isColimit) | (exact GlobalTheory.FpDescent.exists_finitePresentation_model_of_isColimit) | (intros; apply GlobalTheory.FpDescent.exists_finitePresentation_model_of_isColimit  <;> assumption)
