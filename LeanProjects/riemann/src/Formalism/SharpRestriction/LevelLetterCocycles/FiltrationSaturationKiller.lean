import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.GammaSemisimpleLocalOfConsequences
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.HerrClassFieldOfNorms

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def FiltrationPropertiesEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.WachCoordinates.adm7 D HW F Cm

def AdmTools (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm ∧ Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F

def FiltrationPropertiesTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := AdmTools D HW F Cm → FiltrationPropertiesEtale D HW F Cm

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def Pi0LatticeCondition (W : LocWach PD LL O v n) : Prop := ∀ g : W.Gam, ∃ u ∈ W.AΔ, W.γA g W.π₀ = W.π₀ * u

end Core

def GammaPreservesUniformiser (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  Formalism.MainNotions.WachCoordinates.AtCaseA fun l _ K LL h => Pi0LatticeCondition ((HW l).W K 1 LL h.2.2)

def AdmPi0 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F

def UniformiserGammaTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmPi0 D HW F → GammaPreservesUniformiser D HW F

def AdmSat (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFreeGlobal D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F

def SaturationArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm5 D HW F
def SaturationTheoremArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmSat D HW F → SaturationArcLifting D HW F
def SaturationEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.WachCoordinates.adm8 D HW F
def SaturationTheoremEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmSat D HW F → SaturationEtale D HW F

def FirstFiltrationHypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  Formalism.MainNotions.DeltaInvariantLattices.P2 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.Pr2a D HW F ∧ Formalism.MainNotions.HerrComplexNaturality.HerrNaturality D HW F

def FirstFiltrationArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm6 D HW F
def FirstFiltrationTheoremCaseA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := FirstFiltrationHypotheses D HW F → FirstFiltrationArcLifting D HW F
def FirstFiltrationEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.WachCoordinates.adm9 D HW F
def FirstFiltrationTheoremEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := FirstFiltrationHypotheses D HW F → FirstFiltrationEtale D HW F

def SecondFiltrationHypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.P7 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.Pr2b D HW F

def SecondFiltrationArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm7 D HW F
def SecondFiltrationTheoremArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := SecondFiltrationHypotheses D HW F ∧ FirstFiltrationArcLifting D HW F → SecondFiltrationArcLifting D HW F
def SecondFiltrationEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.WachCoordinates.adm10 D HW F
def FamilyMassExplicitOfVolumeAgreement (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := SecondFiltrationHypotheses D HW F ∧ FirstFiltrationEtale D HW F → SecondFiltrationEtale D HW F

def KillerAtLevels (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.ArcLiftingSetup.KillerLevL D.loc D.locA HW F

def AdmKillLev (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F

def KillerLevelsTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := AdmKillLev D HW F Cm → KillerAtLevels D HW F

def KillerBoundWithConstant (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm8 D HW F C

def AdmKillA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := KillerAtLevels D HW F ∧ GammaPreservesUniformiser D HW F

def KillerWithConstantTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := AdmKillA D HW F → KillerBoundWithConstant D HW F C

def KillerAtLevelsSecondForm (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.WachCoordinates.adm11 D HW F

def KillerWachCoordinatesTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := GammaPreservesUniformiser D HW F → KillerAtLevelsSecondForm D HW F

def RootMultiplicityTwo (D : D7) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm9 D

def RelayArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm11 D HW F

def AdmRelayA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F ∧ Formalism.MainNotions.LiftingTheory.ConclusionH D HW F ∧ Formalism.MainNotions.LiftingTheory.ExistsUnitClasses D HW F ∧
    SaturationArcLifting D HW F ∧ FirstFiltrationArcLifting D HW F ∧ SecondFiltrationArcLifting D HW F

def RelayTheoremArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmRelayA D HW F → RelayArcLifting D HW F

def ArcLiftingCoordinates (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm12 D HW F Cm

def AdmArcA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm ∧ Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm ∧ Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F ∧ Formalism.MainNotions.LiftingTheory.ConclusionH D HW F ∧
    Formalism.MainNotions.LiftingTheory.ExistsUnitClasses D HW F ∧ Formalism.MainNotions.LiftingTheory.WachAnnihilatorAll D HW F ∧ SaturationArcLifting D HW F

def ArcCoordinatesTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := AdmArcA D HW F Cm → ArcLiftingCoordinates D HW F Cm

def SplittingArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm13 D HW F Cm

def AdmSplitA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  Formalism.MainNotions.DeltaInvariantLattices.P8 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F ∧ Formalism.MainNotions.LiftingTheory.WachAnnihilatorAll D HW F ∧ Formalism.MainNotions.LiftingTheory.adm23 D HW F ∧
    Formalism.MainNotions.HerrComplexNaturality.HerrExtensionClass D HW F ∧ FirstFiltrationArcLifting D HW F ∧ RelayArcLifting D HW F ∧ ArcLiftingCoordinates D HW F Cm

def SplittingTheoremArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := AdmSplitA D HW F Cm → SplittingArcLifting D HW F Cm

def UniversalComponentCaseA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm14 D HW F Cm

def AdmUnivA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := SaturationArcLifting D HW F ∧ KillerAtLevels D HW F ∧ GammaPreservesUniformiser D HW F ∧ ArcLiftingCoordinates D HW F Cm

def UniversalComponentTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := AdmUnivA D HW F Cm → UniversalComponentCaseA D HW F Cm

def H1fBaseChangeFree (D : D7) : Prop := Formalism.MainNotions.WachCoordinates.adm13 D

def H1fBaseChangeTheorem (D : D7) : Prop := H1fBaseChangeFree D

end Formalism.MainNotions.UnusedSlot80
