import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomAffineHilbertBaseSectionRingHom
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSecAlgTop
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_affineHilbertBaseSectionRingHom : ∀ (Z : Scheme.{0}) (C : Type) [CommRing C] (Φ : C →+* Γ(Z, ⊤)), ∃ h : Z ⟶ Spec (CommRingCat.of C), GlobalTheory.HilbAff.secAlg C h ⊤ = Φ := by
  first | (exact @GlobalTheory.HilbAff.exists_hom_secAlg_top) | (exact GlobalTheory.HilbAff.exists_hom_secAlg_top) | (intros; apply GlobalTheory.HilbAff.exists_hom_secAlg_top  <;> assumption)
