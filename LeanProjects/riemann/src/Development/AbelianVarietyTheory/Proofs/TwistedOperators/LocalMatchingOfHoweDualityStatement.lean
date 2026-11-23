import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalMatchingOfHoweDuality
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_matching_of_howe_duality : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.LocalMatching := by
  first | exact @GlobalTheory.SquareLM.localMatching | exact GlobalTheory.SquareLM.localMatching | (intros; apply GlobalTheory.SquareLM.localMatching <;> assumption)
