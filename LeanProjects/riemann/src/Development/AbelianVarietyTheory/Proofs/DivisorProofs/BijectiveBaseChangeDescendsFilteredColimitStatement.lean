import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveBaseChangeDescendsFilteredColimit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorIff
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_baseChange_descends_filteredColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (R S : Type) [CommRing R] [CommRing S]
    [Algebra (F.obj j) R] [Algebra (F.obj j) S] [Algebra.FinitePresentation (F.obj j) R]
    [Algebra.FinitePresentation (F.obj j) S] (φ : R →ₐ[F.obj j] S), φ.toRingHom.Finite →
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id c.pt c.pt) φ)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id (F.obj k) (F.obj k)) φ) := by
  first | (exact @GlobalTheory.BijDescent.bijective_of_isColimit) | (exact GlobalTheory.BijDescent.bijective_of_isColimit) | (intros; apply GlobalTheory.BijDescent.bijective_of_isColimit  <;> assumption)
