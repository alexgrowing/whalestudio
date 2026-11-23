import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesY
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses3
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFromGramAndBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RecursionOfGramBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadSetBoundOfDegenerationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaBoundFromMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalCoverBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoveringLeFromMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchorBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowDefinitionFromAnchorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepExistenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepGoodReductionStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsBoundOfDeepGoodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingBoundOfDeepGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankBoundOfDeepGoodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimalGenusBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatBoundOfAnchor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeBoundOfDeepGoodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightBoundOfDeepGoodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumConstantOfDeepGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformLowerBoundOfSums
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerBoundOfAllEstimates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightStatementOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShareStatementOfPrintsStatement

open GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.CovTop.AllSteps

theorem covolX_of_scholzeWeinstein (hXH : HypothesesXH) (hSW : GlobalTheory.Published.ScholzeWeinsteinB) (h3 : Hypotheses3)
    (hH : GlobalTheory.CovHt.HypothesesH) (hQ : GlobalTheory.CovHt.Known₂) : CovolX := by
  have hX : HypothesesX := hXH.toClassicalTheoremsX
  have hKS : GlobalTheory.Published.ToroidalForFanKS := hX.ks
  have hN : GlobalTheory.Published.SemiAbelianLieSeminegative := hX.lie
  have hGC : GlobalTheory.Published.GreenCuspidal := hX.green
  have hSep : GlobalTheory.Published.PointSeparationPair := hX.sep
  have hMB : GlobalTheory.Published.MoretBaillyModel := hXH.mb
  have hY : GlobalTheory.CovHt.HypothesesY := hXH.y
  have hP : Hypotheses2 := h3.base
  have hG : GlobalTheory.Published.GrothendieckDeformation := h3.g1
  have hS : GlobalTheory.Published.SiegelToroidalIntegral := hH.sieg
  have hQd : GlobalTheory.HSCore.Quoted := h3.quoted
  have gram : Gram := by apply GlobalTheory.CovTop.gram_of_hypotheses <;> assumption
  have recB : Rec := by apply GlobalTheory.CovTop.rec_of_gram <;> assumption
  have cut : Cut := by apply GlobalTheory.CovTop.cut_of_hypotheses <;> assumption
  have size : Size := GlobalTheory.CovTop.SizeRows.size
  have meas : Meas := by apply GlobalTheory.CovTop.MeasRd.meas <;> assumption
  have rat : GlobalTheory.CovTop.Rat := by apply GlobalTheory.CovTop.rat_of_hypotheses <;> assumption
  have core : CoreLe := by apply GlobalTheory.CoreSlope.coreLe_of_gram_meas_rat <;> assumption
  have anchor : Anchor := by apply GlobalTheory.CovTop.anchor_holds
  have lowDef : LowDef := by apply GlobalTheory.T.low_definition_from_anchor <;> assumption
  have deepEx : DeepEx := by apply GlobalTheory.CovTop.DeepExist.deepEx <;> assumption
  have deepGood : DeepGood := by apply GlobalTheory.T.deep_good_reduction_statement <;> assumption
  have ring : GlobalTheory.CovTop.Ring := by apply GlobalTheory.CovTop.RingStep.ring_of <;> assumption
  have gmin : Gmin := by apply GlobalTheory.CovGminTop.gmin <;> assumption
  have flatDeg : FlatDeg := by apply GlobalTheory.CovTop.FlatDegProof.flatDeg <;> assumption
  have flat : Flat := by apply GlobalTheory.FlatSplit.flat <;> assumption
  have deg : Deg := by apply GlobalTheory.T.degree_bound_of_deep_good <;> assumption
  have share : Share := by apply GlobalTheory.T.share_of_toroidal <;> assumption
  have hs : HS := by apply GlobalTheory.T.height_theorem_of_hypotheses <;> assumption
  have sum : SumC := by apply GlobalTheory.CovTop.sumC_of_deepGood <;> assumption
  have bad : Bad := by apply GlobalTheory.T.bad_set_bound_of_degeneration <;> assumption
  have lam : abelian₂ := by apply GlobalTheory.CovTop.LamAll.lam <;> assumption
  have maps : Maps := by apply GlobalTheory.T.maps_bound_of_deep_good <;> assumption
  have rk : Rk := by apply GlobalTheory.T.rank_bound_of_deep_good <;> assumption
  have height : Height := by apply GlobalTheory.T.height_bound_of_deep_good <;> assumption
  have uLow : ULow := by apply GlobalTheory.CovTop.FromComp.uLow_of <;> assumption
  have low : Low := by apply GlobalTheory.CovTop.LowCover.low <;> assumption
  exact GlobalTheory.CovTop.Assembly.covolX_of_steps gram recB cut bad lam size core low

end GlobalTheory.CovTop.AllSteps
