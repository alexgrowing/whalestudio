import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsLocalizationDescendAway
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_away_unit_map_eq : ∀ (A : Type) [CommRing A] (M : Submonoid A) (u : (Localization M)ˣ), ∃ m ∈ M, ∃ v : (Localization.Away m)ˣ, ∀ φ : Localization.Away m →+* Localization M, φ.comp (algebraMap A _) = algebraMap A _ → Units.map φ.toMonoidHom v = u := by
  first | (exact @GlobalTheory.units_localization_descend_away) | (exact GlobalTheory.units_localization_descend_away) | (intros; apply GlobalTheory.units_localization_descend_away <;> assumption)
