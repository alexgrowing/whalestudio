import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomExtOfAgreeOnFibreDenseOpenSmooth
import Mathlib
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hom_ext_of_agree_on_fibreDense_open_smooth : ∀ (X T Y : Scheme.{0}) (p : X ⟶ T) [Smooth p] (q : Y ⟶ T) [IsSeparated q] (W : X.Opens), (∀ x : X, x ∈ closure ((W : Set X) ∩ p ⁻¹' {p x})) → ∀ f g : X ⟶ Y, f ≫ q = g ≫ q → W.ι ≫ f = W.ι ≫ g → f = g := by
  first | exact @GlobalTheory.FibreDense.main | exact GlobalTheory.FibreDense.main | (intros; apply GlobalTheory.FibreDense.main <;> assumption)
