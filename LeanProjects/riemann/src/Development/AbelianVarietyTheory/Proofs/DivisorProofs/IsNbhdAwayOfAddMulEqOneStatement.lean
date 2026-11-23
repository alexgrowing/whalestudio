import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNbhdAwayOfAddMulEqOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayHomCompAlgebraMap
open GlobalTheory.AffineCurveNbhd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNbhd_away_of_add_algebraMap_mul_eq_one : ∀ (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f : B) (h c : A'), IsNbhd B A' f → h + algebraMap B A' f * c = 1 → IsNbhd B (Localization.Away h) f := by
  first | (exact @GlobalTheory.AffineCurveNbhd.isNbhd_away_of_add_mul_eq_one) | (exact GlobalTheory.AffineCurveNbhd.isNbhd_away_of_add_mul_eq_one) | (intros; apply GlobalTheory.AffineCurveNbhd.isNbhd_away_of_add_mul_eq_one <;> assumption)
