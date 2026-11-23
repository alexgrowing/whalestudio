import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantUniformizer
import Formalism.SharpRestriction.LevelLetterCocycles.ClassMapStep
import Formalism.SharpRestriction.LevelLetterCocycles.ModelKStep
import Formalism.SharpRestriction.LevelLetterCocycles.FirstFrameStepImplication
import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionRingInput
import Formalism.SharpRestriction.LevelLetterCocycles.UpPositionHypothesis

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

def UnivLinkStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (Fo : FonOf D.loc D.locA HW), HerrClassMapsLocal D HW Fo → dvdR →
    invLiftR D HW → classMapR D HW → frameR D HW → modelFR D HW → u1R D HW → kapPiR D HW →
    u2R D HW → DownSlotProposition D HW → UpSlotProposition D HW → MixedSlotProposition D HW → univR D HW

theorem univStep_of (hL : UnivLinkStep) (hd : DvdStep) (hR : InvLiftStep) (hC : ClassMapStep)
    (hH : FrameStep) (hM : ModelFStep) (hU1 : FirstFrameHypothesis) (hk : KapPiStep) (hU2 : SecondPropositionHypothesis)
    (hD : DownSlotHypothesis) (hUp : UpSlotHypothesis) (hMx : MixedSlotHypothesis) : UnivStep :=
  fun D HW F Cm CA CB CK hA =>
    hL D HW F hA.2.2.2.2.1 hd (hR D HW F Cm CA CB CK hA) (hC D HW F Cm CA CB CK hA)
      (hH D HW F Cm CA CB CK hA) (hM D HW F Cm CA CB CK hA) (hU1 D HW F Cm CA CB CK hA)
      (hk D HW F Cm CA CB CK hA) (hU2 D HW F Cm CA CB CK hA) (hD D HW F Cm CA CB CK hA)
      (hUp D HW F Cm CA CB CK hA) (hMx D HW F Cm CA CB CK hA)

theorem local_theorem_of_all_lemmas (hG : GenStep) (hL : LiftStep) (hd : DvdStep) (hq : QuotStep)
    (hn : NormStep) (h9 : DeltaInvariantUniformizer) (he : ExtStep) (hw : WStep) (hk : KerLamStep) (hl : NinLamStep)
    (hg : GradNStep) (hf : FrobPiNStep) (hγ : GamPiStep) (ho : OneGenStep)
    (hUL : UnivLinkStep) (hR : InvLiftStep) (hC : ClassMapStep) (hH : FrameStep) (hM : ModelFStep)
    (hU1 : FirstFrameHypothesis) (hkp : KapPiStep) (hU2 : SecondPropositionHypothesis) (hD : DownSlotHypothesis) (hUp : UpSlotHypothesis)
    (hMx : MixedSlotHypothesis) :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
      (CA CB CK C : ℝ), 160 ≤ C → FontExAll D HW F → IntegralityFromMetric D HW F Cm CA CB CK C :=
  local_theorem_of_lemma_properties hG hL hd hq hn h9 he hw hk hl hg hf hγ ho
    (univStep_of hUL hd hR hC hH hM hU1 hkp hU2 hD hUp hMx)

end Formalism.MainNotions.N.Ln34

end
