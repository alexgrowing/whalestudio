import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPointOfSize
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_point_of_size : Size → WtPt := by
  first | exact @GlobalTheory.RefSum.DivWt.wtPt_of_size | exact GlobalTheory.RefSum.DivWt.wtPt_of_size | (intros; apply GlobalTheory.RefSum.DivWt.wtPt_of_size <;> assumption)
