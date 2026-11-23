import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsThetaMeanSquareNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesY
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NefProd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondJetsMoretBaillyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotingOfPublishedInputsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFromHeightTheoremsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Hypotheses3OfSlim
open GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.CovTop

theorem covolX_of_slim : Slim → HypothesesXH → (∃ r, GlobalTheory.CovTest.Ch2Const r) → CovolX := by
  intro hS hX hC
  obtain ⟨hSW, hP3, hPH⟩ := GlobalTheory.CovTop.hypotheses3_of_slim hS hX.cube
  have hJ := GlobalTheory.T.second_jets_moret_bailly hP3.base hX.mb
  have hQ := GlobalTheory.T.known_of_published_inputs hX hX.y hP3.base hPH hSW hS.poinc hJ hC
  exact GlobalTheory.T.covolume_from_height_theorems hX hSW hP3 hPH hQ

end GlobalTheory.CovTop
