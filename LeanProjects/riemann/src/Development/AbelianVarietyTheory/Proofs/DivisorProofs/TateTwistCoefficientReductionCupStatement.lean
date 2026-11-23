import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCoefficientReductionCup
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCoefficientReduction_cup : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (E : Spc) {n m i j : ℤ} (a : Ht Q E n i) (b : Ht Q E m j), red Q q E _ _ (cup Q a b) = cup q (red Q q E _ _ a) (red Q q E _ _ b) := by
  first | (exact @GlobalTheory.EtC.RedCup.reduction_cup) | (exact GlobalTheory.EtC.RedCup.reduction_cup) | (intros; apply GlobalTheory.EtC.RedCup.reduction_cup  <;> assumption)
