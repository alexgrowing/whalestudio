import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataExtOfOpenCover
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealSheafData_ext_of_openCover' : ∀ {X : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ X),
    (∀ i, IsOpenImmersion (f i)) → (∀ x : X, ∃ i y, f i y = x) →
    ∀ (I I' : X.IdealSheafData), (∀ i, I.comap (f i) = I'.comap (f i)) → I = I' := by
  first | (exact @GlobalTheory.HilbAff.idealSheafData_ext_of_openCover) | (exact GlobalTheory.HilbAff.idealSheafData_ext_of_openCover) | (intros; apply GlobalTheory.HilbAff.idealSheafData_ext_of_openCover  <;> assumption)
