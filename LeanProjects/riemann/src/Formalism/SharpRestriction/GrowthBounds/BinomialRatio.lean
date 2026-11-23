import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FamilyFourthBound
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegmentStatementHolds
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreeAlternative
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.KapCore
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.TopDegreeLeTwoB
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ExtendedStatementOfParts
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.TotalDegreeEplus
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FirstCoefficientFacts
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.LeAndHalfLeProdOneSubExpNegOfBounds
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FinrankTensor
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegLow
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.RankOnDigitsCast
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CardEqChainSum
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.StWeyl
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FactorsOfPerturb
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ChainDim
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.UpperCountOfTopRows
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CountLow
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.BlockInj
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.AiAddMulLeA0
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.BlockFG
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ThresholdStandardLarge
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreeRatioConsecutive
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PairLift
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PairCount
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.NotKept
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.WtBound
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.KeptBlocksOfSLine
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bracket
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.KeptBlocksHolds
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreesLargeOfStd
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseThresholdRatioConsecutive
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SymInt
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.WittPNe
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FinalTheorems
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.DualFlatOf
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.DualLat
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PosCoreLetter
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SettingCharZeroAt
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SettingCZ

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem closed_extendedAllConclusions {D : Formalism.BasicNotions.D7} (h3 : adm3 D) (hU : RestUp) (hL : RestLow) (hL1 : PartnersToFactors)
    (hLift : RestLift) : Closed (ExtendedAllConclusions D) :=
  have hA2 : RemainderSegmentBoundSecond D := restAlt2_of (restSegLow_of hL) (dimHH_of h3) charZeroAt
  closed_of_rests (fun _ _ _ => segment_statement_holds D _ _ _) (restFree D) (remainderSegmentBoundFirst D) (rest2 D) (restAlt3 D)
    (one_segment_of_upper_lower hU hL) hA2 (restExt_of restRk hL1 hLift hA2)

theorem dimYAt_of_adm {D : Formalism.BasicNotions.D7} (hA : admitted D) : DimYAt :=
  dimY_of (D := D) hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.1 (stWeylAt D)

theorem extended_fourth_of_upper_bound {D : Formalism.BasicNotions.D7} {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (h : UpAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    ExtendedDigitRankBound D C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hc j rz ry hd
  exact h X W Qq O Kf ι σ jO w hS hH hc j 0 le_rfl rz ry hd

theorem restUp_of_adm {D : Formalism.BasicNotions.D7} (hA : admitted D) : RestUp :=
  have hY := dimYAt_of_adm hA
  restUp_of blockRankAt hY charZeroAt
    (upper_count_of_top_rows (chainDim_of hY) (numBranch_of hA.2.1 hA.2.2.1) top_rows_bound_holds)

theorem fourth_bound_of_admitted {D : Formalism.BasicNotions.D7} (hA : admitted D) :
    TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc =>
      ExtendedDigitRankBound D C0 CYb Cde Ck CD Cb CE1 CE2 Cc ∧ Conclusion4 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => ⟨extended_fourth_of_upper_bound h, (extended_fourth_of_upper_bound h).toDigitRankBound⟩) (restUp_of_adm hA)

def Open : Prop := RestPairLift

theorem stmtEExt_of {D : Formalism.BasicNotions.D7} (h : admitted D → Open) : ExtendedClosedForm D := fun hA =>
  have hPL := h hA
  have hY := dimYAt_of_adm hA
  have hCD : ChainDimAt := chainDim_of hY
  have hNB : NumBranchAt := numBranch_of hA.2.1 hA.2.2.1
  have hT : RestTail := restTail_of hCD hNB restPairCount (restNotKeptWt_of (wtBound_of hCD) (restBracket_of (restPairFacts_of restNUp) coarse_degrees_large_holds))
  have hK2 : LeadingRowsBeyondThreshold := top_rows_bound_holds
  have hB : BlockRankAt := blockRankAt
  have hK4 : KeptBlocksBeyondThreshold := kept_blocks_holds
  have hL1 : PartnersToFactors := partners_to_factors_holds
  have hCU : RestCountUp := upper_count_of_top_rows hCD hNB hK2
  have hMU : RestMatchUp := restMatchUp_of (restFirstRows_of (restSTopRows_of hK2))
  have hCL : RestCountLow := restCountLow_of'' hCD hT hMU hK4
  closed_extendedAllConclusions hA.2.2.1 (restUp_of hB hY charZeroAt hCU) (restLow_of hB hY charZeroAt hCL) hL1 (restLift_of (restLiftVec_of hPL))

theorem stmtE_of {D : Formalism.BasicNotions.D7} (h : admitted D → Open) : ClosedFormOfAdmitted D := (stmtEExt_of h).closed_of_extended_closed

end Formalism.MainNotions.ColumnSystems.Pf
