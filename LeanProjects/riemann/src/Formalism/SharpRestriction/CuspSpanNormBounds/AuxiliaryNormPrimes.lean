import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.HermitianLattices.StatementMass
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

noncomputable section

namespace Formalism.MainNotions.AuxiliaryNormPrimes

export Formalism.MainNotions.S.UnitaryVolumeMass (embU succMin dualZ)

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt NumberField Matrix Module
open scoped ENNReal NNReal InnerProductSpace

section B3

open Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def aux₃ (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A c : ℝ) : Prop :=
  UnitaryVolumeMass.VolumeRatioBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c

end B3

section Mass

open Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FamilySchurFormalDegree (D : D7) : Prop :=
  UnitaryVolumeMass.stMassRatio D

def GL5LogLValueBoundByZeta (D : D7) : Prop :=
  UnitaryVolumeMass.stMassL D

def RankTwoMassBound (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  UnitaryVolumeMass.stMass2 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C

def MassVolumeForGaugeFamily (D : D7) (G : GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig) : Prop :=
  UnitaryVolumeMass.stMassVol D G

end Mass

section BR

def UnitaryBranchingMultiplicityOne : Prop :=
  UnitaryVolumeMass.stBRmult

def HadamardDeterminantInequality : Prop :=
  UnitaryVolumeMass.stBRhad

def BanaszczykTransferenceBound : Prop :=
  UnitaryVolumeMass.stBRtrans

def MinkowskiFiniteSubgroupOrder : Prop :=
  UnitaryVolumeMass.stBRmink

end BR

section Rows

open Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def CharacterCutVolume (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C

def SpectralWeightsCM (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  UnitaryVolumeMass.stForm D large₂ u u' C' Cl Cg cb Cu cT CT C0 A

end Rows

def TemperatureProductAsymptotic (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 δ : ℝ) : Prop :=
  UnitaryVolumeMass.stTprod D large₂ C' Cl Cg cb Cu cT CT C0 δ

def CriticalTemperatureLowerBound (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0

section Loc

open MeasureTheory Finset Formalism.QuantumDeterminants

variable (D : D7) (large₂ : SizeData₂ D)

def PlancherelBoundOneParameter (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPT D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def PlancherelBoundFiniteSums (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPTsum D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def PlancherelBoundDifferenceOperator (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPTDl D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def BesselDegreeNormalization (C' Cl Cg cb Cu cT CT C0 Cn C1 : ℝ) : Prop :=
  UnitaryVolumeMass.PieriNormDegreeFormula D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1

def DegreeRatioUnitStepBound (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.FormalDegreeUnitStepRatio D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def ArchimedeanMomentBound (C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C : ℝ) : Prop :=
  UnitaryVolumeMass.stMOM D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C

def DimensionConstantBound (C' Cl Cg cb Cu cT CT C0 C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stCONST D large₂ C' Cl Cg cb Cu cT CT C0 C1 C

end Loc

section Comparison₂

open Formalism.MainNotions.S.Lat MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def TermVolumeSmallCellBound (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (u u' : D.what₂.Word) (C1 : ℝ)
    (Y : LoopTie D large₂ X u u' C1) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  UnitaryVolumeMass.stVol D large₂ X u u' C1 Y C' Cl Cg cb Cu cT CT C0 A C

end Comparison₂

section Stmt

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (u u' : D.what₂.Word) (C1 : ℝ) (Y : LoopTie D large₂ X u u' C1)
  (G : letI := D.host.cmStar; GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig)

def admitted (C' Cl Cg cb Cu cT CT C0 A CM CSW δ Cn Cq CPT CDl hilbertNinetyConstant CMo CK CV : ℝ) : Prop :=
  FamilySchurFormalDegree D ∧ GL5LogLValueBoundByZeta D ∧ RankTwoMassBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A CM ∧ MassVolumeForGaugeFamily D G ∧
  UnitaryBranchingMultiplicityOne ∧ HadamardDeterminantInequality ∧ BanaszczykTransferenceBound ∧ MinkowskiFiniteSubgroupOrder ∧
  CharacterCutVolume D large₂ u u' C' Cl Cg cb Cu cT CT C0 A CSW ∧ SpectralWeightsCM D large₂ u u' C' Cl Cg cb Cu cT CT C0 A ∧
  TemperatureProductAsymptotic D large₂ C' Cl Cg cb Cu cT CT C0 δ ∧ CriticalTemperatureLowerBound D large₂ C' Cl Cg cb Cu cT CT C0 ∧
  PlancherelBoundOneParameter D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CPT ∧ PlancherelBoundFiniteSums D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CPT ∧
  PlancherelBoundDifferenceOperator D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CDl ∧ BesselDegreeNormalization D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 ∧
  DegreeRatioUnitStepBound D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 hilbertNinetyConstant ∧ ArchimedeanMomentBound D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Cq CMo ∧
  DimensionConstantBound D large₂ C' Cl Cg cb Cu cT CT C0 C1 CK ∧ TermVolumeSmallCellBound D large₂ X u u' C1 Y C' Cl Cg cb Cu cT CT C0 A CV

def Stmt (C' Cl Cg cb Cu cT CT C0 A CM CSW δ Cn Cq CPT CDl hilbertNinetyConstant CMo CK CV c : ℝ) : Prop :=
  admitted D large₂ X u u' C1 Y G C' Cl Cg cb Cu cT CT C0 A CM CSW δ Cn Cq CPT CDl hilbertNinetyConstant CMo CK CV →
    aux₃ D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c

end Stmt

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def SecondSizeStatement : Prop := ∀ x (i : Fm.Ix x), FamilySchurFormalDegree (Fm.D x i)

def BesselFormLine : Prop := ∀ x (i : Fm.Ix x), GL5LogLValueBoundByZeta (Fm.D x i)

def FamilyRankTwoMassBound (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∃ C, OwnEv Fm fun C' Cl x i => ∀ u u', RankTwoMassBound (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A C

def FamilyGaugeMassVolumes : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), MassVolumeForGaugeFamily (Fm.D x i) (Fm.ex x hx i).gauge

def LocalGenericDensity (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∃ C, OwnEv Fm fun C' Cl x i => ∀ u u', CharacterCutVolume (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A C

def FamilyFormulaUnderLoopData (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => ∀ u u', SpectralWeightsCM (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A

def FamilyTemperatureProductAsymptotic (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  ∀ δ > 0, OwnEv Fm fun C' Cl x i => TemperatureProductAsymptotic (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 δ

def FamilyCriticalTemperatureLower (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => CriticalTemperatureLowerBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0

def FamilyPlancherelOneParameter (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∃ C, ∀ Cn, OwnEv Fm fun C' Cl x i => PlancherelBoundOneParameter (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C

def FamilyPlancherelFiniteSums (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∃ C, ∀ Cn, OwnEv Fm fun C' Cl x i => PlancherelBoundFiniteSums (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C

def FamilyPlancherelDifferenceOperator (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∃ C, ∀ Cn, OwnEv Fm fun C' Cl x i => PlancherelBoundDifferenceOperator (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C

def FamilyBesselDegreeNormalization (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∀ Cn, OwnEv Fm fun C' Cl x i => BesselDegreeNormalization (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1

def FamilyDegreeRatioUnitStep (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∃ C, ∀ Cn, OwnEv Fm fun C' Cl x i => DegreeRatioUnitStepBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C

def FamilyArchimedeanMomentBound (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∀ Cq, ∃ C, ∀ Cn, OwnEv Fm fun C' Cl x i => ArchimedeanMomentBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C

def FamilyDimensionConstantBound (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∃ C, OwnEv Fm fun C' Cl x i => DimensionConstantBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 C1 C

variable (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)

def FamilyTermVolumeBound (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∃ C, OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u',
    TermVolumeSmallCellBound (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1 (Y x hx i u u') C' Cl Cg cb Cu cT CT C0 A C

def AdmF : Prop :=
  SecondSizeStatement Fm ∧ BesselFormLine Fm ∧ FamilyGaugeMassVolumes Fm ∧ UnitaryBranchingMultiplicityOne ∧ HadamardDeterminantInequality ∧ BanaszczykTransferenceBound ∧ MinkowskiFiniteSubgroupOrder ∧
  ∀ Cg cb Cu cT CT C0 A : ℝ,
    FamilyRankTwoMassBound Fm Cg cb Cu cT CT C0 A ∧ LocalGenericDensity Fm Cg cb Cu cT CT C0 A ∧ FamilyFormulaUnderLoopData Fm Cg cb Cu cT CT C0 A ∧ FamilyTemperatureProductAsymptotic Fm Cg cb Cu cT CT C0 ∧ FamilyCriticalTemperatureLower Fm Cg cb Cu cT CT C0 ∧
    FamilyPlancherelOneParameter Fm Cg cb Cu cT CT C0 C1 ∧ FamilyPlancherelFiniteSums Fm Cg cb Cu cT CT C0 C1 ∧ FamilyPlancherelDifferenceOperator Fm Cg cb Cu cT CT C0 C1 ∧ FamilyBesselDegreeNormalization Fm Cg cb Cu cT CT C0 C1 ∧
    FamilyDegreeRatioUnitStep Fm Cg cb Cu cT CT C0 C1 ∧ FamilyArchimedeanMomentBound Fm Cg cb Cu cT CT C0 C1 ∧ FamilyDimensionConstantBound Fm Cg cb Cu cT CT C0 C1 ∧ FamilyTermVolumeBound Fm C1 X Y Cg cb Cu cT CT C0 A

def OrbitValuationBound (c : ℝ) : Prop :=
  0 < c ∧ ∀ Cg cb Cu cT CT C0 A : ℝ,
    OwnEv Fm fun C' Cl x i => ∀ u u', aux₃ (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A c

def KudlaFamilyStatement (c : ℝ) : Prop := AdmF Fm C1 X Y → OrbitValuationBound Fm c

end Family

end Formalism.MainNotions.AuxiliaryNormPrimes
