import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationMaximalIdealEqSpanNilpotentArtinian
import Mathlib
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_maximalIdeal_eq_span_nilpotent_artinian : ∀ (D : Type) [CommRing D] [IsArtinianRing D] (x : D), IsNilpotent x → IsReduced (D ⧸ Ideal.span {x}) → ∀ (P : Ideal D) [P.IsMaximal], IsLocalRing.maximalIdeal (Localization.AtPrime P) = Ideal.span {algebraMap D (Localization.AtPrime P) x} := by
  first | exact @GlobalTheory.localization_maximalIdeal_eq_span_of_nilpotent | exact GlobalTheory.localization_maximalIdeal_eq_span_of_nilpotent | (intros; apply GlobalTheory.localization_maximalIdeal_eq_span_of_nilpotent <;> assumption)
