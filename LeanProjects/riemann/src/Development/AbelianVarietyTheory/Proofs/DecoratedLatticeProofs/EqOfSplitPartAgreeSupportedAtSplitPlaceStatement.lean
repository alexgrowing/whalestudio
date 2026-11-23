import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqOfSplitPartAgreeSupportedAtSplitPlace
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_splitPart_agree_supportedAtSplitPlace : ∀ (D : D7) (S : HSp D) (e : AE D) (h h' : GA D S), IsSplitIdem D e → SuppAt e S h → SuppAt e S h' →
    (∀ i j, e * Formalism.L2.Theta.mt S h i j = e * Formalism.L2.Theta.mt S h' i j) → h = h' := by
  first | exact @GlobalTheory.UnitSplit.eq_of_split_part | exact GlobalTheory.UnitSplit.eq_of_split_part | (intros; apply GlobalTheory.UnitSplit.eq_of_split_part <;> assumption)
