import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeOfHeightPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Hypotheses3OfSlim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Ch2ConstantExistsStatement
open GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.CovTop

theorem covolX_of_slim₂ (hS : Slim) (hX : GlobalTheory.CovTop.HypothesesXH) : CovolX :=
  GlobalTheory.T.covolume_of_height hS hX (GlobalTheory.T.exists_ch2Const_of_prints (GlobalTheory.CovTop.hypotheses3_of_slim hS hX.cube).2.1.base hX.y.alt hX.arr)

example : Slim → HypothesesXH → CovolX := covolX_of_slim₂

end GlobalTheory.CovTop
