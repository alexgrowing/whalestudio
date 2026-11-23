import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalDataRealPlace
import Formalism.SharpRestriction.CuspSpanNormBounds.IsGramNorm
import Formalism.SharpRestriction.CuspSpanNormBounds.PSDKOnOfPSDK
import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyBlockLiftEstimate
import Formalism.SharpRestriction.ParamsHeightRankConstant

open Matrix MeasureTheory NumberField Filter Topology Polynomial
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.RadialChainStatements

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR

export Formalism.MainNotions.S.UnitaryLevelOperators (Jop scalMat mulAfter Op4 op4Mul tens1 tens2 RhOp thLog fsFun Umat modL JL TmatVStar ncGap
  IsPosDefZ zpt fhat headEl headLt levOf haarOf lenI mid3 wnormSq Msq mm minv mdet psiC psiLow psiUp lowOf upOf
  sdScale muLow muUp stabU muStab IsOrbMeas OmG gTC gZW fNorm)

theorem levOf_J {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (μsec : ℂ → Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ)
    (hc : L.c = cStd) (F : (levOf L μsec).GF) : L.J F = lJ (levOf L μsec) (haarOf L μsec) F := by
  funext g
  simp only [LocBessel.J, lJ, hc]
  rfl

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

def SliceBoundC (_D : Formalism.BasicNotions.D7) (Cs : ℝ) : Prop := S.UnitaryLevelOperators.stSlices Cs

def SmoothnessTheoremP (_D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop := S.UnitaryLevelOperators.stSmooth CB

def adm12 (D : Formalism.BasicNotions.D7) (CB Cs : ℝ) : Prop := FrameIntegrationFormula D CB ∧ PositivityTheoremP D CB ∧ SliceBoundC D Cs ∧ SmoothnessTheoremP D CB

def adm13 (D : Formalism.BasicNotions.D7) (c C₁ : ℝ) : Prop := S.UnitaryLevelOperators.stDecay D c C₁

def adm14 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stMarkov

def adm15 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stHerglotz

def adm16 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stPoisson

def SliceBoundE (_D : Formalism.BasicNotions.D7) (Cs : ℝ) : Prop := S.GramWordSpace.Slices Cs

def GermStatement (C₁ C₂ : ℝ) : Prop := S.UnitaryLevelOperators.stGerm C₁ C₂

def adm17 (_D : Formalism.BasicNotions.D7) (C₁ C₂ : ℝ) : Prop := GermStatement C₁ C₂

def adm18 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stJSZ

export Formalism.MainNotions.S.LocalFrameAxioms (LocMatch FrameAx PsiAx k_le_nS Nlet)

def aux₃ (D : D7) (C C' : ℝ) (Kst : ℕ) (Vm : ValMap D.R.k D.R.rS) : Prop := S.LocalFrameAxioms.stThmA D C C' Kst Vm

def admitted (D : Formalism.BasicNotions.D7) (CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ : ℝ) : Prop :=
  adm1 D CB ∧ adm2 D CB ∧ adm3 D ∧ ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D CB ∧ adm7 D ∧ adm8 D CB Co Cd ∧ adm9 D ∧ adm10 D ∧
    adm11 D CB Cv C1 C2 ∧ (adm12 D CB Cs ∧ SliceBoundE D Cs) ∧ adm13 D c C₁ ∧ adm14 D ∧ adm15 D ∧ adm16 D ∧ adm17 D Cg₁ Cg₂ ∧ adm18 D

def Stmt (D : Formalism.BasicNotions.D7) (CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ C C' : ℝ) (Kst : ℕ) (Vm : ValMap D.R.k D.R.rS) : Prop :=
  admitted D CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ → aux₃ D C C' Kst Vm

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
def FamilyTwelfthHypothesis (CB Cs : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm12 (Fm.D x i) CB Cs ∧ SliceBoundE (Fm.D x i) Cs
def FamilyThirteenthHypothesis (c C₁ : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm13 (Fm.D x i) c C₁
def FamilyFourteenthHypothesis : Prop := ∀ x (i : Fm.Ix x), adm14 (Fm.D x i)
def FamilyFifteenthHypothesis : Prop := ∀ x (i : Fm.Ix x), adm15 (Fm.D x i)
def FamilySixteenthHypothesis : Prop := ∀ x (i : Fm.Ix x), adm16 (Fm.D x i)
def FamilyStationaryPhase (Cg₁ Cg₂ : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm17 (Fm.D x i) Cg₁ Cg₂
def FamilyBesselUniqueness : Prop := ∀ x (i : Fm.Ix x), adm18 (Fm.D x i)

def AdmF (CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ : ℝ) : Prop :=
  admF1 Fm CB ∧ admF2 Fm CB ∧ admF3 Fm ∧ admF4 Fm ∧ admF5 Fm ∧ admF6 Fm CB ∧ admF7 Fm ∧ admF8 Fm CB Co Cd ∧ admF9 Fm ∧
    FamilyRowsCountHypothesis Fm ∧ FamilyWeylAndVandermonde Fm CB Cv C1 C2 ∧ FamilyTwelfthHypothesis Fm CB Cs ∧ FamilyThirteenthHypothesis Fm c C₁ ∧ FamilyFourteenthHypothesis Fm ∧ FamilyFifteenthHypothesis Fm ∧ FamilySixteenthHypothesis Fm ∧
    FamilyStationaryPhase Fm Cg₁ Cg₂ ∧ FamilyBesselUniqueness Fm

def OrbitValuationBound (C C' : ℝ) (Kst : ℕ) (Vm : ∀ k r, ValMap k r) : Prop :=
  ∀ x (i : Fm.Ix x), aux₃ (Fm.D x i) C C' Kst (Vm _ _)

def KudlaFamilyStatement (CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ C C' : ℝ) (Kst : ℕ) (Vm : ∀ k r, ValMap k r) : Prop :=
  AdmF Fm CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ → OrbitValuationBound Fm C C' Kst Vm

end Family

def UniformExportStatement (𝒞 : Formalism.MainNotions.FamClass) (Vm : ∀ k r, ValMap k r) : Prop :=
  ∀ CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ : ℝ, ∀ Kst : ℕ, 4 ≤ Kst → ∃ C₀ C'₀ : ℝ, ∀ C ≥ C₀, ∀ C' ≥ C'₀,
    Formalism.MainNotions.Closed 𝒞 (fun Fm _ => KudlaFamilyStatement Fm CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ C C' Kst Vm)

end Formalism.MainNotions.RadialChainStatements

end
