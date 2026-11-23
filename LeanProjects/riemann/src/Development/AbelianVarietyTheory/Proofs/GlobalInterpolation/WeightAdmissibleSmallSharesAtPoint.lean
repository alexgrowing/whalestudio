import Mathlib
import Formalism.SharpRestriction.PageFix
import Formalism.SharpRestriction.Divisibility.SmallFirstModulusBelowScale
import Formalism.SharpRestriction.GlobalSchurBounds.WeightVectorSmallSharesEight
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PageDutiesOfClassSeven

noncomputable section

namespace GlobalTheory.EX.DQ

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

theorem weightAdmissible_smallShares_at_point {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (h : AuxBlock8.admW D L X K) :
    ChW_at X K := by
  have h3 := h.2.2
  unfold AuxBlock8.WReq at h3
  unfold ChW_at
  refine le_of_eq_of_le (Finset.sum_congr rfl fun p _ => ?_) h3
  split_ifs <;> ring

end GlobalTheory.EX.DQ

end
