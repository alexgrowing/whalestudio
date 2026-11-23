import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkGenerizationGermCompat
import Mathlib
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalk_generization_germ_compat : ∀ {X : Scheme.{0}} (x : X) (p : Ideal (X.presheaf.stalk x)) [p.IsPrime], ∃ (q : X) (e : X.presheaf.stalk q ≃+* Localization.AtPrime p), q ⤳ x ∧ ∀ (U : X.Opens) (hq : q ∈ U) (hx : x ∈ U) (s : Γ(X, U)), e ((X.presheaf.germ U q hq).hom s) = algebraMap (X.presheaf.stalk x) (Localization.AtPrime p) ((X.presheaf.germ U x hx).hom s) := by
  first | exact @GlobalTheory.LocalRingGeneralisation.exists_stalk_equiv_localization | exact GlobalTheory.LocalRingGeneralisation.exists_stalk_equiv_localization | (intros; apply GlobalTheory.LocalRingGeneralisation.exists_stalk_equiv_localization <;> assumption)
