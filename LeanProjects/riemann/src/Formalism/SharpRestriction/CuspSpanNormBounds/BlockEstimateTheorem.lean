import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalDataRealPlace
import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyBlockLiftEstimate
import Formalism.SharpRestriction.CuspSpanNormBounds.PSDKOnOfPSDK
import Formalism.SharpRestriction.ParConsts

open Matrix MeasureTheory NumberField Filter Topology Polynomial
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.BlockEstimateTheorem

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR

export Formalism.MainNotions.S.UnitaryLevelOperators (Jop scalMat mulAfter Op4 op4Mul tens1 tens2 RhOp thLog fsFun Umat modL JL TmatVStar ncGap
  IsPosDefZ zpt fhat lenI mid3 wnormSq Msq mm minv mdet psiC psiLow psiUp lowOf upOf sdScale muLow muUp stabU
  muStab IsOrbMeas IsOrbMeasLU OmG gTC gZW fNorm IsKFinCoefT)

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

def GermStatement (C₁ C₂ : ℝ) : Prop := S.UnitaryLevelOperators.stGerm C₁ C₂

def adm17 (_D : Formalism.BasicNotions.D7) (C₁ C₂ : ℝ) : Prop := GermStatement C₁ C₂

def adm18 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stJSZ

export Formalism.MainNotions.S.LocalFrameAxioms (LocMatch FrameAx PsiAx k_le_nS Nlet)

def thmA (D : D7) (C C' : ℝ) (Kst : ℕ) (Vm : ValMap D.R.k D.R.rS) : Prop := S.LocalFrameAxioms.stThmA D C C' Kst Vm

abbrev GM := ∀ k0 r : ℕ, GramWordSpace.GramMap k0 r

def vmOf (D : D7) {k0 : ℕ} (hk : k0 + 1 = D.R.k) (G : GramWordSpace.GramMap k0 D.R.rS) : ValMap D.R.k D.R.rS :=
  hk ▸ G.toValMap

def aux₃ (D : D7) (Gm : GM) (C C' : ℝ) (Kst : ℕ) : Prop :=
  ∀ (k0 : ℕ) (hk : k0 + 1 = D.R.k), thmA D C C' Kst (vmOf D hk (Gm k0 D.R.rS))

def SliceBoundE (D : D7) (Gm : GM) (Ks : ℕ) (E₀ Eg : ℝ) : Prop :=
  ∀ k0 : ℕ, GramWordSpace.TopPos D (Gm k0 D.R.rS) Ks E₀ Eg

def TopLevelPlaneWave (D : D7) (Gm : GM) (Ks : ℕ) (E₀ Eg : ℝ) : Prop :=
  ∀ k0 : ℕ, GramWordSpace.TopWave D (Gm k0 D.R.rS) Ks E₀ Eg

def LowerLevelPositivity (D : D7) (Ks : ℕ) (E₀ Eg : ℝ) : Prop := ∀ k0 : ℕ, GramWordSpace.LowPos D k0 Ks E₀ Eg

def adm23 (_D : D7) : Prop := GramWordSpace.LettersExist

def adm19 (D : D7) (Ks : ℕ) (E₀ Eg : ℝ) : Prop := ∀ k0 : ℕ, GramWordSpace.E D k0 Ks E₀ Eg

def adm20 (D : D7) (Gm : GM) (Ks : ℕ) (E₀ Eg E₁ E₂ : ℝ) : Prop :=
  ∀ k0 : ℕ, GramWordSpace.SingleLevelGramEstimate D (Gm k0 D.R.rS) Ks E₀ Eg E₁ E₂

def adm21 (D : D7) (Gm : GM) (Ks : ℕ) (E₀ Eg E₁ E₂ : ℝ) : Prop :=
  ∀ k0 : ℕ, GramWordSpace.BlockLiftEstimate D (Gm k0 D.R.rS) Ks E₀ Eg E₁ E₂

def adm22 (D : D7) (Gm : GM) (Ks : ℕ) (E₀ Eg E₁ E₂ E₃ : ℝ) : Prop :=
  ∀ k0 : ℕ, GramWordSpace.LargeBlockLiftEstimate D (Gm k0 D.R.rS) Ks E₀ Eg E₁ E₂ E₃

def AdmA (D : D7) (CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ : ℝ) : Prop :=
  adm1 D CB ∧ adm2 D CB ∧ adm3 D ∧ ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D CB ∧ adm7 D ∧ adm8 D CB Co Cd ∧ adm9 D ∧ adm10 D ∧
    adm11 D CB Cv C1 C2 ∧ adm12 D CB Cs ∧ adm13 D c C₁ ∧ adm14 D ∧ adm15 D ∧ adm16 D ∧ adm17 D Cg₁ Cg₂ ∧ adm18 D

def AdmE (D : D7) (Gm : GM) (Ks : ℕ) (E₀ Eg E₁ E₂ E₃ : ℝ) : Prop :=
  SliceBoundE D Gm Ks E₀ Eg ∧ TopLevelPlaneWave D Gm Ks E₀ Eg ∧ adm19 D Ks E₀ Eg ∧ adm20 D Gm Ks E₀ Eg E₁ E₂ ∧
    adm21 D Gm Ks E₀ Eg E₁ E₂ ∧ adm22 D Gm Ks E₀ Eg E₁ E₂ E₃ ∧ LowerLevelPositivity D Ks E₀ Eg ∧ adm23 D

def admitted (D : D7) (Gm : GM) (Ks : ℕ) (CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ E₀ Eg E₁ E₂ E₃ : ℝ) : Prop :=
  AdmA D CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ ∧ AdmE D Gm Ks E₀ Eg E₁ E₂ E₃

def Stmt (D : D7) (Gm : GM) (Kst : ℕ) (CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ E₀ Eg E₁ E₂ E₃ C C' : ℝ) : Prop :=
  admitted D Gm Kst CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ E₀ Eg E₁ E₂ E₃ → aux₃ D Gm C C' Kst

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
def FamilyTopContinuity (Gm : GM) (Ks : ℕ) (E₀ Eg : ℝ) : Prop := ∀ x (i : Fm.Ix x), SliceBoundE (Fm.D x i) Gm Ks E₀ Eg
def FamilyTopPlaneWave (Gm : GM) (Ks : ℕ) (E₀ Eg : ℝ) : Prop := ∀ x (i : Fm.Ix x), TopLevelPlaneWave (Fm.D x i) Gm Ks E₀ Eg
def FamilyLowerLevelPositivity (Ks : ℕ) (E₀ Eg : ℝ) : Prop := ∀ x (i : Fm.Ix x), LowerLevelPositivity (Fm.D x i) Ks E₀ Eg
def FamilyThirteenthHypothesis (c C₁ : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm13 (Fm.D x i) c C₁
def FamilyFourteenthHypothesis : Prop := ∀ x (i : Fm.Ix x), adm14 (Fm.D x i)
def FamilyFifteenthHypothesis : Prop := ∀ x (i : Fm.Ix x), adm15 (Fm.D x i)
def FamilySixteenthHypothesis : Prop := ∀ x (i : Fm.Ix x), adm16 (Fm.D x i)
def FamilyStationaryPhase (Cg₁ Cg₂ : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm17 (Fm.D x i) Cg₁ Cg₂
def FamilyBesselUniqueness : Prop := ∀ x (i : Fm.Ix x), adm18 (Fm.D x i)
def FamilyNineteenthHypothesis (Ks : ℕ) (E₀ Eg : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm19 (Fm.D x i) Ks E₀ Eg
def FamilyTwentiethHypothesis (Gm : GM) (Ks : ℕ) (E₀ Eg E₁ E₂ : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm20 (Fm.D x i) Gm Ks E₀ Eg E₁ E₂
def FamilyTwentyFirstHypothesis (Gm : GM) (Ks : ℕ) (E₀ Eg E₁ E₂ : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm21 (Fm.D x i) Gm Ks E₀ Eg E₁ E₂
def FamilyTwentySecondHypothesis (Gm : GM) (Ks : ℕ) (E₀ Eg E₁ E₂ E₃ : ℝ) : Prop :=
  ∀ x (i : Fm.Ix x), adm22 (Fm.D x i) Gm Ks E₀ Eg E₁ E₂ E₃
def FamilyLiteratureStatements : Prop := ∀ x (i : Fm.Ix x), adm23 (Fm.D x i)

def AdmAF (CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ : ℝ) : Prop :=
  admF1 Fm CB ∧ admF2 Fm CB ∧ admF3 Fm ∧ admF4 Fm ∧ admF5 Fm ∧ admF6 Fm CB ∧ admF7 Fm ∧ admF8 Fm CB Co Cd ∧ admF9 Fm ∧
    FamilyRowsCountHypothesis Fm ∧ FamilyWeylAndVandermonde Fm CB Cv C1 C2 ∧ FamilyTwelfthHypothesis Fm CB Cs ∧ FamilyThirteenthHypothesis Fm c C₁ ∧ FamilyFourteenthHypothesis Fm ∧ FamilyFifteenthHypothesis Fm ∧ FamilySixteenthHypothesis Fm ∧
    FamilyStationaryPhase Fm Cg₁ Cg₂ ∧ FamilyBesselUniqueness Fm

def AdmEF (Gm : GM) (Ks : ℕ) (E₀ Eg E₁ E₂ E₃ : ℝ) : Prop :=
  FamilyTopContinuity Fm Gm Ks E₀ Eg ∧ FamilyTopPlaneWave Fm Gm Ks E₀ Eg ∧ FamilyNineteenthHypothesis Fm Ks E₀ Eg ∧ FamilyTwentiethHypothesis Fm Gm Ks E₀ Eg E₁ E₂ ∧
    FamilyTwentyFirstHypothesis Fm Gm Ks E₀ Eg E₁ E₂ ∧ FamilyTwentySecondHypothesis Fm Gm Ks E₀ Eg E₁ E₂ E₃ ∧ FamilyLowerLevelPositivity Fm Ks E₀ Eg ∧ FamilyLiteratureStatements Fm

def AdmF (Gm : GM) (Ks : ℕ) (CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ E₀ Eg E₁ E₂ E₃ : ℝ) : Prop :=
  AdmAF Fm CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ ∧ AdmEF Fm Gm Ks E₀ Eg E₁ E₂ E₃

def OrbitValuationBound (Gm : GM) (C C' : ℝ) (Kst : ℕ) : Prop := ∀ x (i : Fm.Ix x), aux₃ (Fm.D x i) Gm C C' Kst

def KudlaFamilyStatement (Gm : GM) (Kst : ℕ) (CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ E₀ Eg E₁ E₂ E₃ C C' : ℝ) : Prop :=
  AdmF Fm Gm Kst CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ E₀ Eg E₁ E₂ E₃ → OrbitValuationBound Fm Gm C C' Kst

theorem familyStatement_of_pointwise (Gm : GM) (Kst : ℕ) (CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ E₀ Eg E₁ E₂ E₃ C C' : ℝ)
    (h : ∀ x (i : Fm.Ix x), Stmt (Fm.D x i) Gm Kst CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ E₀ Eg E₁ E₂ E₃ C C') :
    KudlaFamilyStatement Fm Gm Kst CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ E₀ Eg E₁ E₂ E₃ C C' := by
  rintro ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩,
    ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩⟩ x i
  exact h x i ⟨⟨a1 x i, a2 x i, a3 x i, a4 x i, a5 x i, a6 x i, a7 x i, a8 x i, a9 x i, a10 x i, a11 x i, a12 x i,
    a13 x i, a14 x i, a15 x i, a16 x i, a17 x i, a18 x i⟩, ⟨e1 x i, e2 x i, e3 x i, e4 x i, e5 x i, e6 x i, e7 x i, e8 x i⟩⟩

end Family

def UniformExportStatement : Prop :=
  ∀ (Kst : ℕ) (CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ E₀ Eg E₁ E₂ E₃ : ℝ), 4 ≤ Kst → 0 < E₁ → 0 < E₂ → 0 < E₃ →
    ∃ C₀ C'₀ : ℝ, ∀ C ≥ C₀, ∀ C' ≥ C'₀, ∀ (D : D7) (Gm : GM),
      Stmt D Gm Kst CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ E₀ Eg E₁ E₂ E₃ C C'

end Formalism.MainNotions.BlockEstimateTheorem

end
