import Formalism.SharpRestriction.LevelLetterCocycles.SplitROfSteps
import Formalism.SharpRestriction.LevelLetterCocycles.FontExAll

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

def GenStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → genR D

def LiftStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → liftR D

def NormStep : Prop := ∀ D : D7, normR D

def DvdStep : Prop := dvdR

def QuotStep : Prop := ∀ D : D7, adm8 D → adm11 D → quotR D

def DeltaInvariantUniformizer : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    adm1 D HW F Cm → p9R D HW

def ExtStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → extOfR D HW

def WStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → wKillR D HW

def KerLamStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → FontExAll D HW F → kerLamR D HW

def NinLamStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → ninLamR D HW

def GradNStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → gradNR D HW

def FrobPiNStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → frobPiNR D HW

def GamPiStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → gamPiR D HW

def OneGenStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → oneGenR D HW

def UnivStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → univR D HW

theorem killR_of_stepProps (hd : DvdStep) (hq : QuotStep) (hn : NormStep) (h9 : DeltaInvariantUniformizer)
    (he : ExtStep) (hw : WStep) (hk : KerLamStep) (hl : NinLamStep) (hg : GradNStep)
    (hf : FrobPiNStep) (hγ : GamPiStep) (ho : OneGenStep) (hu : UnivStep) :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), FontExAll D HW F → Adm1 D HW F Cm CA CB CK → killR D :=
  fun D HW F Cm CA CB CK hFont hA =>
    killR_of_steps D HW hd (hq D hA.2.2.2.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.2.2.2.2.2.2.1) (hn D)
      (h9 D HW F Cm hA.1)
      (splitR_of_steps D HW F hA.2.1 hA.2.2.2.2.1 (he D HW F Cm CA CB CK hA) (hw D HW F Cm CA CB CK hA)
        (hk D HW F Cm CA CB CK hA hFont) (hl D HW F Cm CA CB CK hA) (hg D HW F Cm CA CB CK hA)
        (hf D HW F Cm CA CB CK hA) (hγ D HW F Cm CA CB CK hA) (ho D HW F Cm CA CB CK hA))
      (hu D HW F Cm CA CB CK hA)

theorem local_theorem_of_lemma_properties (hG : GenStep) (hL : LiftStep) (hd : DvdStep) (hq : QuotStep)
    (hn : NormStep) (h9 : DeltaInvariantUniformizer) (he : ExtStep) (hw : WStep) (hk : KerLamStep) (hl : NinLamStep)
    (hg : GradNStep) (hf : FrobPiNStep) (hγ : GamPiStep) (ho : OneGenStep) (hu : UnivStep) :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
      (CA CB CK C : ℝ), 160 ≤ C → FontExAll D HW F → IntegralityFromMetric D HW F Cm CA CB CK C :=
  fun D HW F Cm CA CB CK C hC hFont =>
    local_theorem_of_three_inputs D HW F Cm CA CB CK C hC (hG D HW F Cm CA CB CK) (hL D HW F Cm CA CB CK)
      (killR_of_stepProps hd hq hn h9 he hw hk hl hg hf hγ ho hu D HW F Cm CA CB CK hFont)

end Formalism.MainNotions.N.Ln34

end
