import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkLocalizationEqGenerization
import Mathlib
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalk_localization_eq_generization : ∀ (X : Scheme.{0}) (x : X) (q : Ideal (X.presheaf.stalk x)) [q.IsPrime], ∃ (y : X) (h : y ⤳ x) (e : Localization.AtPrime q ≃+* X.presheaf.stalk y), ∀ s, e (algebraMap _ _ s) = (X.presheaf.stalkSpecializes h).hom s := by
  first | exact @GlobalTheory.stalk_localization_atPrime_eq_stalk_generization | exact GlobalTheory.stalk_localization_atPrime_eq_stalk_generization | (intros; apply GlobalTheory.stalk_localization_atPrime_eq_stalk_generization <;> assumption)
