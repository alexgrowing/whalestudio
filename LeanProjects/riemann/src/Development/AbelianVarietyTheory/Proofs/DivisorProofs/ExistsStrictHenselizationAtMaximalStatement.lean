import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictHenselizationAtMaximal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_strictHenselization_at_maximal : ∀ (B : Type) [CommRing B] (P : Ideal B) [P.IsMaximal], IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) → ∃ (O : Type) (_ : CommRing O) (_ : Algebra B O), SH O ∧ IndEt B O ∧ ∀ Q : Ideal O, Q.IsMaximal → Q.comap (algebraMap B O) = P ∧ ∀ o : O, ∃ b : B, o - algebraMap B O b ∈ Q := by
  first | (exact @GlobalTheory.HensMax.exists_strictHens_of_maximal) | (exact GlobalTheory.HensMax.exists_strictHens_of_maximal) | (intros; apply GlobalTheory.HensMax.exists_strictHens_of_maximal  <;> assumption)
