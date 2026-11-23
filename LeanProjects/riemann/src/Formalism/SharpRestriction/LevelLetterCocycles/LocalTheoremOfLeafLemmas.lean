import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionFree
import Formalism.SharpRestriction.LevelLetterCocycles.SecondRankCount
import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionHypothesis
import Formalism.SharpRestriction.LevelLetterCocycles.ExpansionFormAll
import Formalism.SharpRestriction.LevelLetterCocycles.UpPositionOfModels

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem local_theorem_of_leaf_lemmas (hG : GenStep) (hL : LiftStep) (hd : DvdStep) (hq : QuotStep)
    (hn : NormStep) (h9 : DeltaInvariantUniformizer) (he : ExtStep) (hw : WStep) (hk : KerLamStep) (hl : NinLamStep)
    (hg : GradNStep) (hf : FrobPiNStep) (hγ : GamPiStep) (ho : OneGenStep)
    (hUL : UnivLinkStep) (hR : InvLiftStep) (hC : ClassMapStep) (hH : FrameStep)
    (hMFL : ModelFLinkStep) (hP5 : ExpansionFormHypothesis) (hML : ModelLStep) (hMQL : ModelQLinkStep)
    (hU1L : FirstFrameOfModels) (hkp : KapPiStep) (hU2L : SecondPropositionOfRank) (hU2R : SecondRankHypothesis)
    (hD : DownSlotOfModels) (hUp : UpSlotOfModels) (hMx : MixedSlotOfModels) :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
      (CA CB CK C : ℝ), 160 ≤ C → FontExAll D HW F → DdRFull D → DiRank D HW F Cm →
        IntegralityFromMetric D HW F Cm CA CB CK C := by
  intro D HW F Cm CA CB CK C hC160 hFont hdr hrk hA
  have hMQ : ModelQStep := modelQStep_of hMQL hML
  have hU2 : SecondPropositionHypothesis := second_proposition_of_models hU2L hMQ hU2R hML
  have hMF := modelFStep_of hMFL hP5 D HW F Cm CA CB CK hdr hrk hA
  have hU1 := first_frame_of_models hU1L hML D HW F Cm CA CB CK hdr hrk hA hMF
  have hUniv : univR D HW :=
    hUL D HW F hA.2.2.2.2.1 hd (hR D HW F Cm CA CB CK hA) (hC D HW F Cm CA CB CK hA)
      (hH D HW F Cm CA CB CK hA) hMF hU1 (hkp D HW F Cm CA CB CK hA) (hU2 D HW F Cm CA CB CK hA)
      (hD D HW F Cm CA CB CK hA hMF) (hUp D HW F Cm CA CB CK hA hMF) (hMx D HW F Cm CA CB CK hA hdr hrk hMF)
  have hKill : killR D :=
    killR_of_steps D HW hd (hq D hA.2.2.2.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.2.2.2.2.2.2.1) (hn D)
      (h9 D HW F Cm hA.1)
      (splitR_of_steps D HW F hA.2.1 hA.2.2.2.2.1 (he D HW F Cm CA CB CK hA) (hw D HW F Cm CA CB CK hA)
        (hk D HW F Cm CA CB CK hA hFont) (hl D HW F Cm CA CB CK hA) (hg D HW F Cm CA CB CK hA)
        (hf D HW F Cm CA CB CK hA) (hγ D HW F Cm CA CB CK hA) (ho D HW F Cm CA CB CK hA))
      hUniv
  exact local_theorem_of_good_extensions D C hC160 (local_form_of_three_inputs D (hG D HW F Cm CA CB CK hA) (hL D HW F Cm CA CB CK hA) hKill)

end Formalism.MainNotions.N.Ln34

end
