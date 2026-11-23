import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity
import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyBlockLiftEstimate
import Formalism.SharpRestriction.ParConsts

open Matrix MeasureTheory Filter Topology Polynomial
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.HereditaryPositivity

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR

export Formalism.MainNotions.S.UnitaryLevelOperators (Jop scalMat mulAfter Op4 op4Mul tens1 tens2 RhOp thLog fsFun Umat modL JL TmatVStar ncGap
  IsPosDefZ zpt fhat lenI mid3 wnormSq)

def adm1 (_D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop := LemmaB CB

def WittOrbitTheorem (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stA_gauge

def adm2b (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stA_herm C

def adm2c (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stA_capelli

def adm3a (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.cuspSpanTopCondition

def IntegralityRemainder (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stA_signs

def RTTRelation (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stB_rtt

def adm5 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stB_det

def HeckeCorrespondenceReflex (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stC_module C

def TelescopingFormStatement (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stC_tele

def ConjugateSelfDualCharacter (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stC_entry

def DualityInequality (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stC_dual C

def PlaneWaveIsometry (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.cuspSpanWaveCondition

def FrameIntegrationFormula (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stD C

def PositivityTheoremP (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stE C

def ArithmeticRiemannRochThetaCond (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stLetters

def LogThetaIdentity (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stThLog

def PlaneWaveLetters (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stWaveLetters

def CapelliEigenvalueAlt (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stCapEig

def adm2 (D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop := WittOrbitTheorem D ∧ adm2b D CB ∧ adm2c D ∧ CapelliEigenvalueAlt D

def adm3b (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.DiagonalEntryIdentity

def adm3 (D : Formalism.BasicNotions.D7) : Prop := adm3a D ∧ adm3b D ∧ IntegralityRemainder D

def ArchimedeanSignatureMatching (D : Formalism.BasicNotions.D7) : Prop := ArithmeticRiemannRochThetaCond D ∧ RTTRelation D

def TorsionSectionsReflex (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stC_rrherm C

def adm6 (D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop := HeckeCorrespondenceReflex D CB ∧ TorsionSectionsReflex D CB

def adm7 (D : Formalism.BasicNotions.D7) : Prop := TelescopingFormStatement D ∧ ConjugateSelfDualCharacter D

def DualityForLists (_D : Formalism.BasicNotions.D7) (C Co Cd : ℝ) : Prop := 0 < Co ∧ S.UnitaryLevelOperators.stDualList C Co Cd

def adm8 (D : Formalism.BasicNotions.D7) (CB Co Cd : ℝ) : Prop := DualityInequality D CB ∧ DualityForLists D CB Co Cd

def IntegrationByPartsAlt (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stIBP

def adm9 (D : Formalism.BasicNotions.D7) : Prop := IntegrationByPartsAlt D ∧ LogThetaIdentity D

def adm10 (D : Formalism.BasicNotions.D7) : Prop := PlaneWaveLetters D ∧ PlaneWaveIsometry D

def adm11 (_D : Formalism.BasicNotions.D7) (CB Cv C1 C2 : ℝ) : Prop := 0 < C1 ∧ S.UnitaryLevelOperators.stLevel CB Cv C1 C2

def SliceBoundC (_D : Formalism.BasicNotions.D7) (Cs : ℝ) : Prop := GramWordSpace.Slices Cs

def SmoothnessTheoremP (_D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop := S.UnitaryLevelOperators.stSmooth CB

def adm12 (D : Formalism.BasicNotions.D7) (CB Cs : ℝ) : Prop := FrameIntegrationFormula D CB ∧ PositivityTheoremP D CB ∧ SliceBoundC D Cs ∧ SmoothnessTheoremP D CB

def adm13 (D : Formalism.BasicNotions.D7) (c C₁ : ℝ) : Prop := S.UnitaryLevelOperators.stDecay D c C₁

def adm14 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stMarkov

def adm15 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stHerglotz

def adm16 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stPoisson

def adm17 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stStatPhase

def adm18 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stJSZ1

abbrev GM := ∀ k0 r : ℕ, GramWordSpace.GramMap k0 r

def Conclusion1 (D : Formalism.BasicNotions.D7) (Ks : ℕ) (C₀ Cg : ℝ) : Prop := ∀ k0 : ℕ, GramWordSpace.E D k0 Ks C₀ Cg

def Conclusion2 (D : Formalism.BasicNotions.D7) (Gm : GM) (Ks : ℕ) (C₀ Cg C₁ C₂ : ℝ) : Prop :=
  ∀ k0 : ℕ, GramWordSpace.SingleLevelGramEstimate D (Gm k0 D.R.rS) Ks C₀ Cg C₁ C₂

def PointsLemma (D : Formalism.BasicNotions.D7) (Gm : GM) (Ks : ℕ) (C₀ Cg C₁ C₂ : ℝ) : Prop :=
  ∀ k0 : ℕ, GramWordSpace.BlockLiftEstimate D (Gm k0 D.R.rS) Ks C₀ Cg C₁ C₂

def Conclusion4 (D : Formalism.BasicNotions.D7) (Gm : GM) (Ks : ℕ) (C₀ Cg C₁ C₂ C₃ : ℝ) : Prop :=
  ∀ k0 : ℕ, GramWordSpace.LargeBlockLiftEstimate D (Gm k0 D.R.rS) Ks C₀ Cg C₁ C₂ C₃

def aux₃ (D : Formalism.BasicNotions.D7) (Gm : GM) (Ks : ℕ) (C₀ Cg C₁ C₂ C₃ : ℝ) : Prop :=
  Conclusion1 D Ks C₀ Cg ∧ Conclusion2 D Gm Ks C₀ Cg C₁ C₂ ∧ PointsLemma D Gm Ks C₀ Cg C₁ C₂ ∧ Conclusion4 D Gm Ks C₀ Cg C₁ C₂ C₃

def LowerLevelPositivity (D : Formalism.BasicNotions.D7) (Ks : ℕ) (C₀ Cg : ℝ) : Prop := ∀ k0 : ℕ, GramWordSpace.LowPos D k0 Ks C₀ Cg

def SliceBoundE (D : Formalism.BasicNotions.D7) (Gm : GM) (Ks : ℕ) (C₀ Cg : ℝ) : Prop :=
  ∀ k0 : ℕ, GramWordSpace.TopPos D (Gm k0 D.R.rS) Ks C₀ Cg

def TopLevelPlaneWave (D : Formalism.BasicNotions.D7) (Gm : GM) (Ks : ℕ) (C₀ Cg : ℝ) : Prop :=
  ∀ k0 : ℕ, GramWordSpace.TopWave D (Gm k0 D.R.rS) Ks C₀ Cg

def admitted (D : Formalism.BasicNotions.D7) (Gm : GM) (CB Co Cd Cv C1 C2 Cs c C₁ : ℝ) (Ks : ℕ) (C₀ Cg : ℝ) : Prop :=
  adm1 D CB ∧ adm2 D CB ∧ adm3 D ∧ ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D CB ∧ adm7 D ∧ adm8 D CB Co Cd ∧ adm9 D ∧ adm10 D ∧
    adm11 D CB Cv C1 C2 ∧ adm12 D CB Cs ∧ SliceBoundE D Gm Ks C₀ Cg ∧ TopLevelPlaneWave D Gm Ks C₀ Cg ∧ LowerLevelPositivity D Ks C₀ Cg ∧ adm13 D c C₁ ∧
    adm14 D ∧ adm15 D ∧ adm16 D ∧ adm17 D ∧ adm18 D

def Stmt (D : Formalism.BasicNotions.D7) (Gm : GM) (CB Co Cd Cv C1 C2 Cs c Cd₁ : ℝ) (Ks : ℕ) (C₀ Cg C₁ C₂ C₃ : ℝ) : Prop :=
  admitted D Gm CB Co Cd Cv C1 C2 Cs c Cd₁ Ks C₀ Cg → aux₃ D Gm Ks C₀ Cg C₁ C₂ C₃

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def admF1 (CB : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm1 (Fm.D x i) CB
def admF2 (CB : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm2 (Fm.D x i) CB
def admF3 : Prop := ∀ x (i : Fm.Ix x), adm3 (Fm.D x i)
def admF4 : Prop := ∀ x (i : Fm.Ix x), ArchimedeanSignatureMatching (Fm.D x i)
def admF5 : Prop := ∀ x (i : Fm.Ix x), adm5 (Fm.D x i)
def admF6 (CB : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm6 (Fm.D x i) CB
def admF7 : Prop := ∀ x (i : Fm.Ix x), adm7 (Fm.D x i)
def admF8 (CB Co Cd : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm8 (Fm.D x i) CB Co Cd
def admF9 : Prop := ∀ x (i : Fm.Ix x), adm9 (Fm.D x i)
def FamilyRowsCountHypothesis : Prop := ∀ x (i : Fm.Ix x), adm10 (Fm.D x i)
def FamilyWeylAndVandermonde (CB Cv C1 C2 : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm11 (Fm.D x i) CB Cv C1 C2
def FamilyTwelfthHypothesis (CB Cs : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm12 (Fm.D x i) CB Cs
def FamilyTopContinuity (Gm : GM) (Ks : ℕ) (C₀ Cg : ℝ) : Prop := ∀ x (i : Fm.Ix x), SliceBoundE (Fm.D x i) Gm Ks C₀ Cg
def FamilyTopPlaneWave (Gm : GM) (Ks : ℕ) (C₀ Cg : ℝ) : Prop := ∀ x (i : Fm.Ix x), TopLevelPlaneWave (Fm.D x i) Gm Ks C₀ Cg
def FamilyLowerLevelPositivity (Ks : ℕ) (C₀ Cg : ℝ) : Prop := ∀ x (i : Fm.Ix x), LowerLevelPositivity (Fm.D x i) Ks C₀ Cg
def FamilyThirteenthHypothesis (c C₁ : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm13 (Fm.D x i) c C₁
def FamilyFourteenthHypothesis : Prop := ∀ x (i : Fm.Ix x), adm14 (Fm.D x i)
def FamilyFifteenthHypothesis : Prop := ∀ x (i : Fm.Ix x), adm15 (Fm.D x i)
def FamilySixteenthHypothesis : Prop := ∀ x (i : Fm.Ix x), adm16 (Fm.D x i)
def FamilyStationaryPhase : Prop := ∀ x (i : Fm.Ix x), adm17 (Fm.D x i)
def FamilyBesselUniqueness : Prop := ∀ x (i : Fm.Ix x), adm18 (Fm.D x i)

def AdmF (Gm : GM) (CB Co Cd Cv C1 C2 Cs c C₁ : ℝ) (Ks : ℕ) (C₀ Cg : ℝ) : Prop :=
  admF1 Fm CB ∧ admF2 Fm CB ∧ admF3 Fm ∧ admF4 Fm ∧ admF5 Fm ∧ admF6 Fm CB ∧ admF7 Fm ∧ admF8 Fm CB Co Cd ∧ admF9 Fm ∧
    FamilyRowsCountHypothesis Fm ∧ FamilyWeylAndVandermonde Fm CB Cv C1 C2 ∧ FamilyTwelfthHypothesis Fm CB Cs ∧ FamilyTopContinuity Fm Gm Ks C₀ Cg ∧ FamilyTopPlaneWave Fm Gm Ks C₀ Cg ∧
    FamilyLowerLevelPositivity Fm Ks C₀ Cg ∧ FamilyThirteenthHypothesis Fm c C₁ ∧ FamilyFourteenthHypothesis Fm ∧ FamilyFifteenthHypothesis Fm ∧ FamilySixteenthHypothesis Fm ∧ FamilyStationaryPhase Fm ∧ FamilyBesselUniqueness Fm

def ConclusionF1 (Ks : ℕ) (C₀ Cg : ℝ) : Prop := ∀ x (i : Fm.Ix x), Conclusion1 (Fm.D x i) Ks C₀ Cg

def ConclusionF2 (Gm : GM) (Ks : ℕ) (C₀ Cg C₁ C₂ : ℝ) : Prop :=
  ∀ x (i : Fm.Ix x), Conclusion2 (Fm.D x i) Gm Ks C₀ Cg C₁ C₂

def ConclusionF3 (Gm : GM) (Ks : ℕ) (C₀ Cg C₁ C₂ : ℝ) : Prop :=
  ∀ x (i : Fm.Ix x), PointsLemma (Fm.D x i) Gm Ks C₀ Cg C₁ C₂

def FamilyEstimateFour (Gm : GM) (Ks : ℕ) (C₀ Cg C₁ C₂ C₃ : ℝ) : Prop :=
  ∀ x (i : Fm.Ix x), Conclusion4 (Fm.D x i) Gm Ks C₀ Cg C₁ C₂ C₃

def OrbitValuationBound (Gm : GM) (Ks : ℕ) (C₀ Cg C₁ C₂ C₃ : ℝ) : Prop :=
  ConclusionF1 Fm Ks C₀ Cg ∧ ConclusionF2 Fm Gm Ks C₀ Cg C₁ C₂ ∧ ConclusionF3 Fm Gm Ks C₀ Cg C₁ C₂ ∧ FamilyEstimateFour Fm Gm Ks C₀ Cg C₁ C₂ C₃

def KudlaFamilyStatement (Gm : GM) (CB Co Cd Cv C1 C2 Cs c Cd₁ : ℝ) (Ks : ℕ) (C₀ Cg C₁ C₂ C₃ : ℝ) : Prop :=
  AdmF Fm Gm CB Co Cd Cv C1 C2 Cs c Cd₁ Ks C₀ Cg → OrbitValuationBound Fm Gm Ks C₀ Cg C₁ C₂ C₃

end Family

def UniformExportStatement (Gm : GM) : Prop :=
  ∀ (Ks : ℕ) (CB Co Cd Cv C1 C2 Cs c Cd₁ : ℝ), ∃ C₁ C₂ C₃ C₀₀ Cg₀ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
    ∀ C₀ ≥ C₀₀, ∀ Cg ≥ Cg₀, ∀ D : Formalism.BasicNotions.D7, Stmt D Gm CB Co Cd Cv C1 C2 Cs c Cd₁ Ks C₀ Cg C₁ C₂ C₃

end Formalism.MainNotions.HereditaryPositivity

end
