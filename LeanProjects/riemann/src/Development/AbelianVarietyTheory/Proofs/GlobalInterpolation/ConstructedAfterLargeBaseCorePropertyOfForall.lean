import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeServiceGlobalReciprocityStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowAAtGAtBuilt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DivisionSecondComplementConstructedPoints
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowCountsOfLinkedTies
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowJOnOfRowHPA
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PeriodEntriesAtBuilt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassCountBoundParamsLambdaConstructedPoints
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowHInstROfHU
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LPrjSurjAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WorkingFamClassCopiesEqFrozen
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RealTiedSetDiv
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LoopRowOfFiniteDim
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OffK0Closed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowPositivityOfSiegelWeil
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RanksFramesOfSiegelWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartitionSelectionEvaluation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowOfCovolumeOntoGrid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowHTwOfTie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowRepresentationBasePosition
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

namespace GlobalTheory.Fc.AllAtMember

section large₂

variable {KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop} {Q Q' : V4.Slot}

theorem eventually_coreProperty_mono {r r' : V4.Slot → Prop} (h : Lg1 KP Q Q' r) (hi : ∀ S, r S → r' S) : Lg1 KP Q Q' r' :=
  let ⟨R, hR, h⟩ := h; ⟨R, hR, hi _ h⟩

theorem forall_linked_bundles_and {Lk : LkT Bundle} {H H' : ∀ 𝒜 : FamClass, RawSel Bundle 𝒜 → Prop}
    (h : Lg1 KP Q Q' fun S => Row S Lk H) (h' : Lg1 KP Q Q' fun S => Row S Lk H') :
    Lg1 KP Q Q' fun S => Row S Lk fun 𝒜 σ => H 𝒜 σ ∧ H' 𝒜 σ :=
  RowL.and (KP := KP) (Q := Q) (Q' := Q') h h'

end large₂

def recSpec (D : D7) (O : Obj D) (c : ℝ) (b : Bundle D O c) : Σ R : Formalism.L2.RecT O.ex, Formalism.L2.SG.SpectralTiesReal.STiesR R := ⟨b.R, b.S⟩

end GlobalTheory.Fc.AllAtMember
