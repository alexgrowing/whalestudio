import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveVectorQuadraticLevelMeasure
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_residue_approximation : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (P : Ideal B), P.IsMaximal → ∀ (Q : Ideal D) (g : D), g ∉ Q → Q.comap (algebraMap B D) = P → (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) → ∀ a : Localization.Away g, ∃ b : B, a - algebraMap B (Localization.Away g) b ∈ Q.map (algebraMap D (Localization.Away g)) := by
  first | (exact @GlobalTheory.residue_surj_localizationAway) | (exact GlobalTheory.residue_surj_localizationAway) | (intros; apply GlobalTheory.residue_surj_localizationAway <;> assumption)
