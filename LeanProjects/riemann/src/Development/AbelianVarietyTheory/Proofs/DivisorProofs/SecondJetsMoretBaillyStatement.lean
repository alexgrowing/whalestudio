import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondJetsMoretBailly
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsThetaMeanSquareNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.second_jets_moret_bailly : Hypotheses2 → GlobalTheory.Published.MoretBaillyModel → GlobalTheory.LieHt.SecJets4 := by
  first | exact @GlobalTheory.SecJetLem.secJets4 | exact GlobalTheory.SecJetLem.secJets4 | (intros; apply GlobalTheory.SecJetLem.secJets4 <;> assumption)
