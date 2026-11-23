import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafComapEqOfOpenCover
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idealSheaf_comap_eq_of_openCover : ∀ {X : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ X),
    (∀ i, IsOpenImmersion (f i)) → (∀ x : X, ∃ i y, f i y = x) →
    ∀ (J : ∀ i, (V i).IdealSheafData),
    (∀ i j (Y : Scheme.{0}) (a : Y ⟶ V i) (a' : Y ⟶ V j), a ≫ f i = a' ≫ f j →
      (J i).comap a = (J j).comap a') →
    ∃ I : X.IdealSheafData, ∀ i, I.comap (f i) = J i := by
  first | (exact @GlobalTheory.IdealGlue.exists_comap_eq) | (exact GlobalTheory.IdealGlue.exists_comap_eq) | (intros; apply GlobalTheory.IdealGlue.exists_comap_eq <;> assumption)
