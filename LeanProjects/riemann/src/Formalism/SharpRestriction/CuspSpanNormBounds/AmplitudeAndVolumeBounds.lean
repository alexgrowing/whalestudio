import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
import Formalism.HermitianLattices.StatementMass
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

noncomputable section

namespace Formalism.MainNotions.VanishingOnXAndXPlus

export Formalism.MainNotions.S.UnitaryVolumeMass (embU succMin dualZ ForAmpH absMinor)

open NumberField Matrix Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal NNReal InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section B3

variable (D : D7)

abbrev Stand (u u' : D.what₂.Word) : Prop := Cnt.Stand D u u'

abbrev Hyp0 (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop := Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0

abbrev Hyp (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A

def aux₃ (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A c : ℝ) : Prop :=
  UnitaryVolumeMass.VolumeRatioBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c

end B3

section Lat

variable (D : D7)

def adm11 (u u' : D.what₂.Word) : Prop :=
  UnitaryVolumeMass.stLem1At D u (Tu D u')

def adm12 (u u' : D.what₂.Word) : Prop :=
  UnitaryVolumeMass.stLem2At D u (Tu D u')

def adm13 (u u' : D.what₂.Word) : Prop :=
  UnitaryVolumeMass.HyperplaneRankAtWord D u (Tu D u')

def adm14 (u u' : D.what₂.Word) : Prop :=
  UnitaryVolumeMass.stThmAAt D u (Tu D u')

def adm15 (u u' : D.what₂.Word) : Prop :=
  UnitaryVolumeMass.stThmBAt D u (Tu D u')

end Lat

section MassBR

variable (D : D7)

def adm3a : Prop :=
  UnitaryVolumeMass.stMassRatio D

def adm3b : Prop :=
  UnitaryVolumeMass.stMassL D

def IntegralityRemainder (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  UnitaryVolumeMass.stMass2 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C

def DoublingBasicIdentity' (G : GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig) : Prop :=
  UnitaryVolumeMass.stMassVol D G

def BranchingMultiplicityVariant : Prop :=
  UnitaryVolumeMass.stBRmult

def MinkowskiCounting : Prop :=
  UnitaryVolumeMass.stBRhad

def HeckeCommutation : Prop :=
  UnitaryVolumeMass.stBRtrans

def MinkowskiSubgroupOrderBound : Prop :=
  UnitaryVolumeMass.stBRmink

end MassBR

section Lines

variable (D : D7)

def adm6 (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 δ : ℝ) : Prop :=
  UnitaryVolumeMass.stTprod D large₂ C' Cl Cg cb Cu cT CT C0 δ

def adm7 (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0

def adm8 (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  UnitaryVolumeMass.stForm D large₂ u u' C' Cl Cg cb Cu cT CT C0 A

def adm9 (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stSchur D large₂ C' Cl Cg cb Cu cT CT C0 C1 C

def PlaneWaveLetters : Prop :=
  UnitaryVolumeMass.stWeyl D

def PlaneWaveIsometry (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
    ∀ (w : D.what₂.Word) (τ : D.what₂.Tau),
      (dimPiU D.R.k (uS D w τ) : ℝ) = vand (uS D w τ) / ∏ i ∈ Finset.range D.R.k, (i.factorial : ℝ)

end Lines

section Counts

variable (D : D7)

def ArchimedeanSignatureMatching (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C

def adm16 (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C c : ℝ) : Prop :=
  UnitaryVolumeMass.stX D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C c

def LatticeGenusVolumeLemma : Prop :=
  UnitaryVolumeMass.stLem3 D

def TotalMassIdentityForWord (u : D.what₂.Word) : Prop :=
  UnitaryVolumeMass.stLem3L0 D u

def adm18 (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  UnitaryVolumeMass.congruence_at_split_frobenius_holds D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C

def adm19 (large₂ : SizeData₂ D) (CH C : ℝ) : Prop :=
  UnitaryVolumeMass.SubmoduleIndexCount D large₂ CH C

def adm20 (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A Ad C : ℝ) : Prop :=
  UnitaryVolumeMass.MeanFlagPairCount D large₂ u u' C' Cl Cg cb Cu cT CT C0 A Ad C

def adm21 (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  UnitaryVolumeMass.PartnerCountBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C

end Counts

section Loc

open MeasureTheory Finset Formalism.QuantumDeterminants

variable (D : D7) (large₂ : SizeData₂ D)

def ArthurRepresentationUpDown (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPT D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def ShareLowerBound (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPTsum D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def PlancherelDifferenceBound (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPTDl D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def DegreeNormalizationFormula (C' Cl Cg cb Cu cT CT C0 Cn C1 : ℝ) : Prop :=
  UnitaryVolumeMass.PieriNormDegreeFormula D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1

def FormalDegreeUnitShiftRatio (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.FormalDegreeUnitStepRatio D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def adm2 (C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C : ℝ) : Prop :=
  UnitaryVolumeMass.stMOM D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C

end Loc

section Amp

open MeasureTheory Finset Formalism.QuantumDeterminants

variable (D : D7) (large₂ : SizeData₂ D)

def adm22 (C' Cl Cg cb Cu cT CT C0 _A C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stCONST D large₂ C' Cl Cg cb Cu cT CT C0 C1 C

def L2HilbertSchmidtPointwise (C' Cl Cg cb Cu cT CT C0 A C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.L2PointwiseLoss D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C

def L2LossProductBound (C' Cl Cg cb Cu cT CT C0 A C C2 Ch : ℝ) : Prop :=
  UnitaryVolumeMass.stL2prod D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch

def OperatorNormPointwiseBound (C' Cl Cg cb Cu cT CT C0 A C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stABS D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C

def AbsoluteConvergenceBesselIntegral (C' Cl Cg cb Cu cT CT C0 A C1 : ℝ) : Prop :=
  UnitaryVolumeMass.stABSconv D large₂ C' Cl Cg cb Cu cT CT C0 A C1

def AbsoluteLossProductBound (C' Cl Cg cb Cu cT CT C0 A C C2 Ch : ℝ) : Prop :=
  UnitaryVolumeMass.stABSprod D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch

def HerrExtensionClause (C' Cl Cg cb Cu cT CT C0 A C1 C δ : ℝ) : Prop :=
  UnitaryVolumeMass.stMIN D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C δ

def adm26 (C' Cl Cg cb Cu cT CT C0 A C1 Cpr C Ch δ : ℝ) : Prop :=
  UnitaryVolumeMass.stDEC D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Cpr C Ch δ

def AmplitudeBoundsConjunction (C' Cl Cg cb Cu cT CT C0 A C1 Cpr C C2 Ch δ : ℝ) : Prop :=
  adm22 D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C ∧ L2HilbertSchmidtPointwise D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C ∧
  L2LossProductBound D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch ∧ OperatorNormPointwiseBound D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C ∧
  AbsoluteConvergenceBesselIntegral D large₂ C' Cl Cg cb Cu cT CT C0 A C1 ∧ AbsoluteLossProductBound D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch ∧ HerrExtensionClause D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C δ ∧
  adm26 D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Cpr C Ch δ

end Amp

section HHb

variable (D : D7)

def HerrCocycleExtensionClass (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  UnitaryVolumeMass.stHH D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C

end HHb

section Comparison₂

def TermVolumeSmallCellBound (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (u u' : D.what₂.Word) (C1 : ℝ)
    (Y : LoopTie D large₂ X u u' C1) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  UnitaryVolumeMass.stVol D large₂ X u u' C1 Y C' Cl Cg cb Cu cT CT C0 A C

end Comparison₂

section Stmt

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (u u' : D.what₂.Word) (C1 : ℝ) (Y : LoopTie D large₂ X u u' C1)
  (G : GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig)

def Adm3 (C' Cl Cg cb Cu cT CT C0 A CM CSW δ Cn Cq CPT CDl hilbertNinetyConstant CMo CS : ℝ) : Prop :=
  ArthurRepresentationUpDown D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CPT ∧ ShareLowerBound D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CPT ∧
  PlancherelDifferenceBound D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CDl ∧ DegreeNormalizationFormula D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 ∧
  FormalDegreeUnitShiftRatio D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 hilbertNinetyConstant ∧ adm2 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Cq CMo ∧
  adm3a D ∧ adm3b D ∧ IntegralityRemainder D large₂ u u' C' Cl Cg cb Cu cT CT C0 A CM ∧ DoublingBasicIdentity' D G ∧
  ArchimedeanSignatureMatching D large₂ u u' C' Cl Cg cb Cu cT CT C0 A CSW ∧
  BranchingMultiplicityVariant ∧ MinkowskiCounting ∧ HeckeCommutation ∧ MinkowskiSubgroupOrderBound ∧
  adm6 D large₂ C' Cl Cg cb Cu cT CT C0 δ ∧ adm7 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ adm8 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A ∧
  adm9 D large₂ C' Cl Cg cb Cu cT CT C0 C1 CS ∧ PlaneWaveLetters D ∧ PlaneWaveIsometry D large₂ C' Cl Cg cb Cu cT CT C0

def Adm3b (C' Cl Cg cb Cu cT CT C0 A CX cX IncreasingRowChoicePerColumn LocalCohomologySetup CC2 Ad CC3 CC4 Cpr Ca Ca2 Ch δm CH : ℝ) : Prop :=
  adm11 D u u' ∧ adm12 D u u' ∧ adm13 D u u' ∧ adm14 D u u' ∧ adm15 D u u' ∧
  adm16 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A CX cX ∧ LatticeGenusVolumeLemma D ∧ TotalMassIdentityForWord D u ∧
  adm18 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A IncreasingRowChoicePerColumn ∧ adm19 D large₂ LocalCohomologySetup CC2 ∧
  adm20 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A Ad CC3 ∧ adm21 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A CC4 ∧
  AmplitudeBoundsConjunction D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Cpr Ca Ca2 Ch δm ∧
  HerrCocycleExtensionClass D large₂ u u' C' Cl Cg cb Cu cT CT C0 A CH

def admitted (C' Cl Cg cb Cu cT CT C0 A CM CSW δ Cn Cq CPT CDl hilbertNinetyConstant CMo CS CX cX IncreasingRowChoicePerColumn LocalCohomologySetup CC2 Ad CC3 CC4 Cpr Ca Ca2 Ch δm CH CV : ℝ) :
    Prop :=
  Adm3 D large₂ u u' C1 G C' Cl Cg cb Cu cT CT C0 A CM CSW δ Cn Cq CPT CDl hilbertNinetyConstant CMo CS ∧
  Adm3b D large₂ u u' C1 C' Cl Cg cb Cu cT CT C0 A CX cX IncreasingRowChoicePerColumn LocalCohomologySetup CC2 Ad CC3 CC4 Cpr Ca Ca2 Ch δm CH ∧
  TermVolumeSmallCellBound D large₂ X u u' C1 Y C' Cl Cg cb Cu cT CT C0 A CV

def Stmt (C' Cl Cg cb Cu cT CT C0 A CM CSW δ Cn Cq CPT CDl hilbertNinetyConstant CMo CS CX cX IncreasingRowChoicePerColumn LocalCohomologySetup CC2 Ad CC3 CC4 Cpr Ca Ca2 Ch δm CH CV c : ℝ) :
    Prop :=
  admitted D large₂ X u u' C1 Y G C' Cl Cg cb Cu cT CT C0 A CM CSW δ Cn Cq CPT CDl hilbertNinetyConstant CMo CS CX cX IncreasingRowChoicePerColumn LocalCohomologySetup CC2 Ad CC3 CC4 Cpr Ca Ca2
      Ch δm CH CV →
    aux₃ D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c

end Stmt

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def FamilyOneParameterPlancherelBound (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∃ C, ∀ Cn, OwnEv Fm fun C' Cl x i => ArthurRepresentationUpDown (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C

def FamilyFiniteSumPlancherelBound (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∃ C, ∀ Cn, OwnEv Fm fun C' Cl x i => ShareLowerBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C

def FamilyPlancherelDifferenceBound (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∃ C, ∀ Cn, OwnEv Fm fun C' Cl x i => PlancherelDifferenceBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C

def FamilyDegreeNormalization (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∀ Cn, OwnEv Fm fun C' Cl x i => DegreeNormalizationFormula (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1

def FamilyFormalDegreeUnitShiftRatio (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∃ C, ∀ Cn, OwnEv Fm fun C' Cl x i => FormalDegreeUnitShiftRatio (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C

def admF2 (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∀ Cq, ∃ C, ∀ Cn, OwnEv Fm fun C' Cl x i => adm2 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C

def FamilyFirstVolumeHypothesis : Prop := ∀ x (i : Fm.Ix x), adm3a (Fm.D x i)

def FamilySecondVolumeHypothesis : Prop := ∀ x (i : Fm.Ix x), adm3b (Fm.D x i)

def FamilyRankTwoMassEstimate (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∃ C, OwnEv Fm fun C' Cl x i => ∀ u u', IntegralityRemainder (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A C

def FamilyMassVolumeForGauge : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), DoublingBasicIdentity' (Fm.D x i) (Fm.ex x hx i).gauge

def admF4 (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∃ C, OwnEv Fm fun C' Cl x i => ∀ u u', ArchimedeanSignatureMatching (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A C

def admF6 (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  ∀ δ > 0, OwnEv Fm fun C' Cl x i => adm6 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 δ

def admF7 (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => adm7 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0

def admF8 (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => ∀ u u', adm8 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A

def admF9 (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∃ C, OwnEv Fm fun C' Cl x i => adm9 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 C1 C

def FamilyRowsExist : Prop := ∀ x (i : Fm.Ix x), PlaneWaveLetters (Fm.D x i)

def FamilyWeylDimensionVandermondeQuotient (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => PlaneWaveIsometry (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0

def FamilyWeylAndVandermonde : Prop := ∀ x (i : Fm.Ix x) u u', adm11 (Fm.D x i) u u'

def FamilyTwelfthHypothesis : Prop := ∀ x (i : Fm.Ix x) u u', adm12 (Fm.D x i) u u'

def FamilyThirteenthHypothesis : Prop := ∀ x (i : Fm.Ix x) u u', adm13 (Fm.D x i) u u'

def FamilyFourteenthHypothesis : Prop := ∀ x (i : Fm.Ix x) u u', adm14 (Fm.D x i) u u'

def FamilyFifteenthHypothesis : Prop := ∀ x (i : Fm.Ix x) u u', adm15 (Fm.D x i) u u'

def FamilySixteenthHypothesis (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∃ C c, OwnEv Fm fun C' Cl x i => ∀ u u', adm16 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A C c

def FamilyRowMassIdentity : Prop := ∀ x (i : Fm.Ix x), LatticeGenusVolumeLemma (Fm.D x i)

def FamilyTotalRowMassIdentity : Prop := ∀ x, Fm.x1 < x → ∀ (i : Fm.Ix x) u, TotalMassIdentityForWord (Fm.D x i) u

def FamilyBesselUniqueness (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∃ C₀, ∀ C ≥ C₀, OwnEv Fm fun C' Cl x i => ∀ u u', adm18 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A C

def FamilyNineteenthHypothesis : Prop := ∃ C, ∀ CH, ∃ x0, ∀ x ≥ x0, ∀ i : Fm.Ix x, adm19 (Fm.D x i) (Fm.L x i) CH C

def FamilyTwentiethHypothesis (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∀ Ad, ∃ C₀, ∀ C ≥ C₀, OwnEv Fm fun C' Cl x i => ∀ u u', adm20 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A Ad C

def FamilyTwentyFirstHypothesis (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∃ C, OwnEv Fm fun C' Cl x i => ∀ u u', adm21 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A C

def FamilyAmplitudeBoundsShared (Cg cb Cu cT CT C0 A C1 : ℝ) : Prop :=
  ∃ C C2 Ch, ∀ Cpr, ∀ δ > 0, OwnEv Fm fun C' Cl x i =>
    AmplitudeBoundsConjunction (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cpr C C2 Ch δ

def FamilyTermMassEstimate (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∃ C, OwnEv Fm fun C' Cl x i => ∀ u u', HerrCocycleExtensionClass (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A C

variable (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)

def FamilyTermVolumeSmallCellBound (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∃ C, OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u',
    TermVolumeSmallCellBound (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1 (Y x hx i u u') C' Cl Cg cb Cu cT CT C0 A C

def AdmF : Prop :=
  FamilyFirstVolumeHypothesis Fm ∧ FamilySecondVolumeHypothesis Fm ∧ FamilyMassVolumeForGauge Fm ∧ BranchingMultiplicityVariant ∧ MinkowskiCounting ∧ HeckeCommutation ∧ MinkowskiSubgroupOrderBound ∧ FamilyRowsExist Fm ∧
  FamilyWeylAndVandermonde Fm ∧ FamilyTwelfthHypothesis Fm ∧ FamilyThirteenthHypothesis Fm ∧ FamilyFourteenthHypothesis Fm ∧ FamilyFifteenthHypothesis Fm ∧ FamilyRowMassIdentity Fm ∧ FamilyTotalRowMassIdentity Fm ∧ FamilyNineteenthHypothesis Fm ∧
  ∀ Cg cb Cu cT CT C0 A : ℝ,
    FamilyOneParameterPlancherelBound Fm Cg cb Cu cT CT C0 C1 ∧ FamilyFiniteSumPlancherelBound Fm Cg cb Cu cT CT C0 C1 ∧ FamilyPlancherelDifferenceBound Fm Cg cb Cu cT CT C0 C1 ∧
    FamilyDegreeNormalization Fm Cg cb Cu cT CT C0 C1 ∧ FamilyFormalDegreeUnitShiftRatio Fm Cg cb Cu cT CT C0 C1 ∧ admF2 Fm Cg cb Cu cT CT C0 C1 ∧
    FamilyRankTwoMassEstimate Fm Cg cb Cu cT CT C0 A ∧ admF4 Fm Cg cb Cu cT CT C0 A ∧ admF6 Fm Cg cb Cu cT CT C0 ∧
    admF7 Fm Cg cb Cu cT CT C0 ∧ admF8 Fm Cg cb Cu cT CT C0 A ∧ admF9 Fm Cg cb Cu cT CT C0 C1 ∧
    FamilyWeylDimensionVandermondeQuotient Fm Cg cb Cu cT CT C0 ∧ FamilySixteenthHypothesis Fm Cg cb Cu cT CT C0 A ∧
    FamilyBesselUniqueness Fm Cg cb Cu cT CT C0 A ∧ FamilyTwentiethHypothesis Fm Cg cb Cu cT CT C0 A ∧ FamilyTwentyFirstHypothesis Fm Cg cb Cu cT CT C0 A ∧
    FamilyAmplitudeBoundsShared Fm Cg cb Cu cT CT C0 A C1 ∧ FamilyTermMassEstimate Fm Cg cb Cu cT CT C0 A ∧ FamilyTermVolumeSmallCellBound Fm C1 X Y Cg cb Cu cT CT C0 A

def OrbitValuationBound (c : ℝ) : Prop :=
  0 < c ∧ ∀ Cg cb Cu cT CT C0 A : ℝ,
    OwnEv Fm fun C' Cl x i => ∀ u u', aux₃ (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A c

def KudlaFamilyStatement (c : ℝ) : Prop := AdmF Fm C1 X Y → OrbitValuationBound Fm c

end Family

end Formalism.MainNotions.VanishingOnXAndXPlus

end
