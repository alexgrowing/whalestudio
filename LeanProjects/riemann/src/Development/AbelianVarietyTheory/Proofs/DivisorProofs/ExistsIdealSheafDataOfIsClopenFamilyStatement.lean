import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDataOfIsClopenFamily
import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamIdeal
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idealSheafData_of_isClopen_family : ∀ (Z : Scheme.{0}) (W : Set Z), IsClopen W → ∀ (F : ∀ U : Z.affineOpens, Ideal Γ(Z, U)),
    (∀ (U : Z.affineOpens) (f : Γ(Z, U)), (U : Set Z) ⊆ W →
      (F U).map (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom = F (Z.affineBasicOpen f)) →
    ∃ J : Z.IdealSheafData, (∀ U : Z.affineOpens, (U : Set Z) ⊆ W → J.ideal U = F U) ∧
      (J.support : Set Z) ⊆ W := by
  first | exact @GlobalTheory.ClopenIdealSheaf.exists_idealSheafData_of_isClopen | exact GlobalTheory.ClopenIdealSheaf.exists_idealSheafData_of_isClopen | (intros; apply GlobalTheory.ClopenIdealSheaf.exists_idealSheafData_of_isClopen <;> assumption)
