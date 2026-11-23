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

namespace Formalism.MainNotions.VanishingOnXAndXPlusMass

export Formalism.MainNotions.S.UnitaryVolumeMass (embU succMin dualZ)

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal NNReal InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Conclusion₂

variable (D : D7)

def Conclusion1 (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C c : ℝ) : Prop :=
  UnitaryVolumeMass.stX D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C c

def Conclusion2 : Prop :=
  UnitaryVolumeMass.stLem3 D

def PointsLemma (u : D.what₂.Word) : Prop :=
  UnitaryVolumeMass.stLem3L0 D u

def Conclusion4 (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  UnitaryVolumeMass.congruence_at_split_frobenius_holds D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C

def Conclusion5 (large₂ : SizeData₂ D) (CH C : ℝ) : Prop :=
  UnitaryVolumeMass.SubmoduleIndexCount D large₂ CH C

def Conclusion6 (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A Ad C : ℝ) : Prop :=
  UnitaryVolumeMass.MeanFlagPairCount D large₂ u u' C' Cl Cg cb Cu cT CT C0 A Ad C

def division_rows_rational_lattice (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  UnitaryVolumeMass.PartnerCountBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C

end Conclusion₂

section admitted

variable (D : D7)

def adm1 : Prop :=
  UnitaryVolumeMass.stMassRatio D

def adm2 : Prop :=
  UnitaryVolumeMass.stMassL D

def adm16 (G : GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig) : Prop :=
  UnitaryVolumeMass.stMassVol D G

def adm3 : Prop :=
  UnitaryVolumeMass.stBRmult

def ArchimedeanSignatureMatching : Prop :=
  UnitaryVolumeMass.stBRhad

def adm14 : Prop :=
  UnitaryVolumeMass.stBRtrans

def adm15 : Prop :=
  UnitaryVolumeMass.stBRmink

def adm5 : Prop :=
  UnitaryVolumeMass.stLem1 D

def adm6 : Prop :=
  UnitaryVolumeMass.HyperplaneRankAllWords D

def adm7 (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C

def adm20 (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  UnitaryVolumeMass.stForm D large₂ u u' C' Cl Cg cb Cu cT CT C0 A

def adm8 (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 δ : ℝ) : Prop :=
  UnitaryVolumeMass.stTprod D large₂ C' Cl Cg cb Cu cT CT C0 δ

def adm9 (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0

end admitted

section Loc

open MeasureTheory Finset Formalism.QuantumDeterminants

variable (D : D7) (large₂ : SizeData₂ D)

def adm10 (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPT D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def adm11 (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPTsum D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def adm12 (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPTDl D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def adm17 (C' Cl Cg cb Cu cT CT C0 Cn C1 : ℝ) : Prop :=
  UnitaryVolumeMass.PieriNormDegreeFormula D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1

def adm18 (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.FormalDegreeUnitStepRatio D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def adm13 (C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C : ℝ) : Prop :=
  UnitaryVolumeMass.stMOM D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C

def adm19 (C' Cl Cg cb Cu cT CT C0 C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stCONST D large₂ C' Cl Cg cb Cu cT CT C0 C1 C

end Loc

section Stmt

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (G : GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig)

def admitted (C' Cl Cg cb Cu cT CT C0 A CSW δ Cn C1 Cq CPT CDl hilbertNinetyConstant CMo CK : ℝ) : Prop :=
  adm1 D ∧ adm2 D ∧ adm3 ∧ ArchimedeanSignatureMatching ∧ adm5 D ∧ adm6 D ∧
  adm7 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A CSW ∧ adm8 D large₂ C' Cl Cg cb Cu cT CT C0 δ ∧ adm9 D large₂ C' Cl Cg cb Cu cT CT C0 ∧
  adm10 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CPT ∧ adm11 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CPT ∧ adm12 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CDl ∧
  adm13 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Cq CMo ∧ adm14 ∧ adm15 ∧ adm16 D G ∧
  adm17 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 ∧ adm18 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 hilbertNinetyConstant ∧ adm19 D large₂ C' Cl Cg cb Cu cT CT C0 C1 CK ∧
  adm20 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A

def Conclusion₂ (C' Cl Cg cb Cu cT CT C0 A Ad CH C c : ℝ) : Prop :=
  Conclusion1 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C c ∧ Conclusion2 D ∧ PointsLemma D u ∧ Conclusion4 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C ∧ Conclusion5 D large₂ CH C ∧
  Conclusion6 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A Ad C ∧ division_rows_rational_lattice D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C

def Stmt (C' Cl Cg cb Cu cT CT C0 A CSW δ Cn C1 Cq CPT CDl hilbertNinetyConstant CMo CK Ad CH C c : ℝ) : Prop :=
  admitted D large₂ u u' G C' Cl Cg cb Cu cT CT C0 A CSW δ Cn C1 Cq CPT CDl hilbertNinetyConstant CMo CK → Conclusion₂ D large₂ u u' C' Cl Cg cb Cu cT CT C0 A Ad CH C c

end Stmt

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def familyUnitInput : Prop := ∀ x (i : Fm.Ix x), adm1 (Fm.D x i)

def FamilySecondHypothesis : Prop := ∀ x (i : Fm.Ix x), adm2 (Fm.D x i)

def FamilyFifthHypothesis : Prop := ∀ x (i : Fm.Ix x), adm5 (Fm.D x i)

def FamilySixthHypothesis : Prop := ∀ x (i : Fm.Ix x), adm6 (Fm.D x i)

def adm7F (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∃ C, OwnEv Fm fun C' Cl x i => ∀ u u', adm7 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A C

def FamilyTemperatureAsymptotic (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  ∀ δ > 0, OwnEv Fm fun C' Cl x i => adm8 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 δ

def proportionalityInputFamily (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => adm9 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0

def compactDualInputFamily (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∃ C, ∀ Cn, OwnEv Fm fun C' Cl x i => adm10 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C

def ComplementTwoFamily (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∃ C, ∀ Cn, OwnEv Fm fun C' Cl x i => adm11 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C

def FamilyPlancherelBound (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∃ C, ∀ Cn, OwnEv Fm fun C' Cl x i => adm12 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C

def ComplementCountFamily (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∀ Cq, ∃ C, ∀ Cn, OwnEv Fm fun C' Cl x i => adm13 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C

def FullRankFamily : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), adm16 (Fm.D x i) (Fm.ex x hx i).gauge

def FamilyBesselNormalizationBound (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∀ Cn, OwnEv Fm fun C' Cl x i => adm17 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1

def G1Family (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∃ C, ∀ Cn, OwnEv Fm fun C' Cl x i => adm18 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C

def LogTermFamily (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∃ C, OwnEv Fm fun C' Cl x i => adm19 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 C1 C

def G3BoundFamily (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => ∀ u u', adm20 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A

def AdmF : Prop :=
  familyUnitInput Fm ∧ FamilySecondHypothesis Fm ∧ adm3 ∧ ArchimedeanSignatureMatching ∧ FamilyFifthHypothesis Fm ∧ FamilySixthHypothesis Fm ∧ adm14 ∧ adm15 ∧ FullRankFamily Fm ∧
  ∀ Cg cb Cu cT CT C0 A C1 : ℝ,
    adm7F Fm Cg cb Cu cT CT C0 A ∧ FamilyTemperatureAsymptotic Fm Cg cb Cu cT CT C0 ∧ proportionalityInputFamily Fm Cg cb Cu cT CT C0 ∧
    compactDualInputFamily Fm Cg cb Cu cT CT C0 C1 ∧ ComplementTwoFamily Fm Cg cb Cu cT CT C0 C1 ∧ FamilyPlancherelBound Fm Cg cb Cu cT CT C0 C1 ∧
    ComplementCountFamily Fm Cg cb Cu cT CT C0 C1 ∧ FamilyBesselNormalizationBound Fm Cg cb Cu cT CT C0 C1 ∧ G1Family Fm Cg cb Cu cT CT C0 C1 ∧
    LogTermFamily Fm Cg cb Cu cT CT C0 C1 ∧ G3BoundFamily Fm Cg cb Cu cT CT C0 A

def Conclusion1Family (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∃ C c, OwnEv Fm fun C' Cl x i => ∀ u u', Conclusion1 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A C c

def Conclusion2Family : Prop := ∀ x (i : Fm.Ix x), Conclusion2 (Fm.D x i)

def Conclusion3Family : Prop := ∀ x, Fm.x1 < x → ∀ (i : Fm.Ix x) u, PointsLemma (Fm.D x i) u

def SlopeLemmaFamily (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∃ C₀, ∀ C ≥ C₀, OwnEv Fm fun C' Cl x i => ∀ u u', Conclusion4 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A C

def SlopeLossFamily : Prop := ∃ C, ∀ CH, ∃ x0, ∀ x ≥ x0, ∀ i : Fm.Ix x, Conclusion5 (Fm.D x i) (Fm.L x i) CH C

def Conclusion6Family (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∀ Ad, ∃ C₀, ∀ C ≥ C₀, OwnEv Fm fun C' Cl x i => ∀ u u', Conclusion6 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A Ad C

def FamilyRankTwoMassConclusion (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∃ C, OwnEv Fm fun C' Cl x i => ∀ u u', division_rows_rational_lattice (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A C

def ConclusionOnFamily : Prop :=
  Conclusion2Family Fm ∧ Conclusion3Family Fm ∧ SlopeLossFamily Fm ∧
  ∀ Cg cb Cu cT CT C0 A : ℝ,
    Conclusion1Family Fm Cg cb Cu cT CT C0 A ∧ SlopeLemmaFamily Fm Cg cb Cu cT CT C0 A ∧ Conclusion6Family Fm Cg cb Cu cT CT C0 A ∧
    FamilyRankTwoMassConclusion Fm Cg cb Cu cT CT C0 A

def KudlaFamilyStatement : Prop := AdmF Fm → ConclusionOnFamily Fm

end Family

end Formalism.MainNotions.VanishingOnXAndXPlusMass

end
