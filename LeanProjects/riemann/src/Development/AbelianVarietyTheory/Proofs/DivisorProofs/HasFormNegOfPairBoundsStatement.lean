import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFormNegOfPairBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasForm_neg_of_pair_bounds : GlobalTheory.RealLift.FormEx → ∀ (P Q R S : ℕ) (x : ℚ) (k k' : ℕ), P ≤ S → Q ≤ R → 0 < k → 0 < k' → x - Formalism.BasicNotions.TH.cPair S R = k → x + Formalism.BasicNotions.TH.cPair S R = k' → GlobalTheory.RealLift.HasForm P Q R S (-x) := by
  first | exact @GlobalTheory.RealLift.hasForm_neg_of_formEx | exact GlobalTheory.RealLift.hasForm_neg_of_formEx | (intros; apply GlobalTheory.RealLift.hasForm_neg_of_formEx <;> assumption)
