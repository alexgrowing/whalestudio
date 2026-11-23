import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Ch2ConstantExists
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ch2Const_of_prints : Hypotheses2 → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ArithRiemannRoch → ∃ r, GlobalTheory.CovTest.Ch2Const r := by
  first | exact @GlobalTheory.ThetaRegularityConstant.exists_ch2Const | exact GlobalTheory.ThetaRegularityConstant.exists_ch2Const | (intros; apply GlobalTheory.ThetaRegularityConstant.exists_ch2Const <;> assumption)
