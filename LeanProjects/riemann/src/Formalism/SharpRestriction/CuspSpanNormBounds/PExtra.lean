import Formalism.SharpRestriction.CuspSpanNormBounds.RadialChainStatements
import Formalism.SharpRestriction.CuspSpanNormBounds.HereditaryPositivity
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import Formalism.SharpRestriction.CuspSpanNormBounds.NonGenericAndKTwoTheorems
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeIndexAndWeightTheory
import Formalism.SharpRestriction.CuspSpanNormBounds.UniformConstantsAndStatements
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusProjectedBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.AdmissibleBoundsFromSource
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl

noncomputable section

namespace Formalism.MainNotions.PX

section GroupS0

open Formalism.BasicNotions Formalism.MainNotions.S NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def H0 (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  StandingNumericalData D C0 ∧ StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT ∧ 1 ≤ C0

def Under {eps : ℝ} (Fm : FamP eps) (P : ∀ x (i : Fm.Ix x), Prop) : Prop :=
  ∀ C0 Cg cb Cu cT CT : ℝ, OwnEv Fm fun C' Cl x i => H0 (Fm.D x i) (Fm.L x i) C0 C' Cl Cg cb Cu cT CT → P x i

def UnderG {eps : ℝ} (Fm : FamP eps) (P : ∀ x, Fm.x1 < x → ∀ _ : Fm.Ix x, Prop) : Prop :=
  ∀ C0 Cg cb Cu cT CT : ℝ, OwnEv Fm fun C' Cl x i => ∀ hx : Fm.x1 < x,
    H0 (Fm.D x i) (Fm.L x i) C0 C' Cl Cg cb Cu cT CT → P x hx i

def Exp (D : D7) : Prop := ∀ u u' : D.what₂.Word, KExpansion D.s u u' ∧ KAbsConv D.s u u'

def IdCell (D : D7) : Prop := ∀ u : D.what₂.Word, IdCellDiag D.s u

def TwoA (D : D7) : Prop := ∀ (u u' : D.what₂.Word) (Φ : Set (D.s.Term u u')), IsSat D Φ →
  Summable (fun p : pairsIn D.s Φ => ‖D.s.pval p.1‖) →
    hsNormSq (KOf D.s u u' Φ) ≤ (∏ᶠ p ∈ typedPl D, (1 + 3 / (Ideal.absNorm p.asIdeal : ℝ))) * gaG D *
      (∑' p : pairsIn D.s Φ, D.s.pval p.1).re

def TwoAg (D : D7) : Prop := ∀ (u u' : D.what₂.Word) (Φ : Set (D.s.Term u u')), IsSat D Φ →
  Summable (fun p : pairsIn D.s Φ => ‖D.s.pval p.1‖) →
    hsNormSq (KOf D.s u u' Φ) ≤
      (∏ i : Fin 2, (1 + 3 / (D.host.g i : ℝ))) ^ D.R.f * gaG D * (∑' p : pairsIn D.s Φ, D.s.pval p.1).re

def V0 (D : D7) : Prop := ∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), ¬ D.s.relevant t → D.s.aTerm u u' t = 0

def GDr (D : D7) (X : TermTie D) : Prop :=
  ∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), D.s.Gterm t ≠ 0 →
    Dl (X.fl t).fl (X.fl' t).fl (D.R.rS + 1) ≠ 0 ∧
    (Dl (X.fl t).fl (X.fl' t).fl D.R.rS ≠ 0 → ∀ τ, 0 < (embS D τ (Lat.Gval (X.fl t) (X.fl' t))).re)

def IdentityCellVanishes (D : D7) : Prop := ∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), D.s.isId t → D.s.Gterm t = 0

def FirstSumAtLeastOne (D : D7) : Prop := ∀ (u u' : D.what₂.Word) (p : D.s.Pair u u'),
  D.s.Gterm (D.s.pfst p) ≠ 0 → D.s.Gterm (D.s.psnd p) ≠ 0 → 1 ≤ D.s.s0 p

def PairAbs (D : D7) : Prop := ∀ u u' : D.what₂.Word, Summable (fun p : D.s.Pair u u' => ‖D.s.pval p‖)

section Family

variable {eps : ℝ} (Fm : FamP eps)

def ExpF : Prop := Under Fm fun x i => Exp (Fm.D x i)
def IdCellF : Prop := Under Fm fun x i => IdCell (Fm.D x i)
def TwoAF : Prop := Under Fm fun x i => TwoA (Fm.D x i)
def TwoAgF : Prop := Under Fm fun x i => TwoAg (Fm.D x i)
def FamilyVanishingCondition : Prop := Under Fm fun x i => V0 (Fm.D x i)
def GDrF (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)) : Prop :=
  UnderG Fm fun x hx i => GDr (Fm.D x i) (At x hx i)
def FamilyIdentityCondition : Prop := Under Fm fun x i => IdentityCellVanishes (Fm.D x i)
def FamilyFirstSumAtLeastOne : Prop := Under Fm fun x i => FirstSumAtLeastOne (Fm.D x i)
def PairAbsF : Prop := Under Fm fun x i => PairAbs (Fm.D x i)

def CellsF (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)) : Prop := NonGenericAndKTwoTheorems.admF6 Fm At

def FixedF : Prop := ∀ gc : AdmissibleBoundsFromSource.GivC, AdmissibleBoundsFromSource.FamilySixteenthHypothesis Fm gc

def MassVolF (Gv : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Cnt.GaugeVol (Fm.D x i)) : Prop := NonGenericAndKTwoTheorems.FamilyComplementMassVolumes Fm Gv

def MassVolGF : Prop := LatticeIndexAndWeightTheory.FamilyComplementMassVolumes Fm

def DuMassF : Prop := LatticeIndexAndWeightTheory.FamilyTwelfthHypothesis Fm

def MainF (g : UniformConstantsAndStatements.Given) (C Ce : ℝ) : Prop := UniformConstantsAndStatements.admF8 Fm g C Ce

def KFinDecayF (c0 : ℝ) : Prop := CayleySignature.admF3 Fm c0

def FamilyExpansionWithConstants (C0 Cg cb Cu cT CT Ca : ℝ) : Prop := LocalBesselAndTopKernel.FamilyExpansion Fm C0 Cg cb Cu cT CT Ca

def RanksF (C0 Cg cb Cu cT CT : ℝ) : Prop := LocalBesselAndTopKernel.FamilyRanksHypothesis Fm C0 Cg cb Cu cT CT

def DensF : Prop := LocalBesselAndTopKernel.FamilyDensity Fm

def CntF {X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)}
    (Z : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LocalSplitGroups.TermLocs (Fm.D x i) (X x hx i))
    (cN : ∀ x (i : Fm.Ix x), (Fm.D x i).what₂.Word → (Fm.D x i).what₂.Word → ℝ) : Prop := LocalBesselAndTopKernel.FamilyFormalDegreeDecay Fm Z cN

def FormF (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)) (Cw : ℝ)
    (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) u u', LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' Cw) (Vm : ∀ k r, ValMap k r)
    (C0 Cg cb Cu cT CT : ℝ) : Prop := LocalBesselAndTopKernel.FamilyFormulaUnderLoopData Fm X Cw Y Vm C0 Cg cb Cu cT CT

def ArithF (cN : ∀ x (i : Fm.Ix x), (Fm.D x i).what₂.Word → (Fm.D x i).what₂.Word → ℝ) (C0 Cg cb Cu cT CT : ℝ) : Prop :=
  LocalBesselAndTopKernel.FamilyArithmetic Fm cN C0 Cg cb Cu cT CT

def SizeF : Prop := NonGenericAndKTwoTheorems.admF8 Fm

def FamilyFunctionalOrderWithConstant (C : ℝ) : Prop := CayleySignature.FamilyFunctionalOrder Fm C

end Family

def ModelBasics : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Formalism.MainNotions.S.Loc.Model F E), M.OK →
    (∀ a : E, (∀ b ∈ M.R, M.psiR (a * b) = 1) ↔ a ∈ M.R) ∧
    (∀ (m : ℕ) (ZZ : M.Mat m), (Nat.card (M.Cok ZZ) : ℝ) = (M.modK (ZZ.Z.map M.R.subtype).det)⁻¹)

end GroupS0

section GroupS1

open Formalism.MainNotions.S

def lemmaB (CB : ℝ) : Prop := TopsChoicePartA.LemmaB CB

def t22 : Prop := UnitaryLevelOperators.DiagonalEntryIdentity

def LetterIdentitiesRTT : Prop := UnitaryLevelOperators.stLetters

def dualList (C Co Cd : ℝ) : Prop := UnitaryLevelOperators.stDualList C Co Cd

def PointwiseIntegrationByParts : Prop := UnitaryLevelOperators.stIBP

def ConjugationIdentity : Prop := UnitaryLevelOperators.stThLog

def PlaneWaveLetterIdentities : Prop := UnitaryLevelOperators.stWaveLetters

def slices (Cs : ℝ) : Prop := UnitaryLevelOperators.stSlices Cs

def slicesOrb (Cs : ℝ) : Prop := GramWordSpace.Slices Cs

def lettersExist : Prop := GramWordSpace.LettersExist

def lowPos (D : Formalism.BasicNotions.D7) (Ks : ℕ) (C₀ Cg : ℝ) : Prop := ∀ k0 : ℕ, GramWordSpace.LowPos D k0 Ks C₀ Cg

def smooth (CB : ℝ) : Prop := UnitaryLevelOperators.stSmooth CB

def topPos (D : Formalism.BasicNotions.D7) (Gm : HereditaryPositivity.GM) (Ks : ℕ) (C₀ Cg : ℝ) : Prop := HereditaryPositivity.SliceBoundE D Gm Ks C₀ Cg

def topWave (D : Formalism.BasicNotions.D7) (Gm : HereditaryPositivity.GM) (Ks : ℕ) (C₀ Cg : ℝ) : Prop := HereditaryPositivity.TopLevelPlaneWave D Gm Ks C₀ Cg

def decay (D : Formalism.BasicNotions.D7) (c C₁ : ℝ) : Prop := UnitaryLevelOperators.stDecay D c C₁

def germ (C₁ C₂ : ℝ) : Prop := UnitaryLevelOperators.stGerm C₁ C₂

def LettersOnCells (D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop := OnePlaceEstimates.adm12 D CB

structure shortGrids (D : Formalism.BasicNotions.D7) (Gm : HereditaryPositivity.GM) (CB Cs C₃ : ℝ) : Prop where
  e72 : OnePlaceEstimates.ShortGridGramBound D Gm CB Cs
  e73 : OnePlaceEstimates.LiftGridGramBound D Gm CB Cs
  e74 : OnePlaceEstimates.LargeBlockGridBound D Gm CB Cs C₃
  sup : OnePlaceEstimates.UniformGridGramBound D Gm CB Cs C₃

def s3d0 (D : Formalism.BasicNotions.D7) (Ch Cg Cq : ℝ) : Prop := OnePlaceEstimates.adm22 D Ch Cg Cq

structure S1 (CB Co Cd Cs Cg₁ Cg₂ : ℝ) : Prop where
  lemmaB : lemmaB CB
  t22 : t22
  LetterIdentitiesRTT : LetterIdentitiesRTT
  dualList : dualList CB Co Cd
  PointwiseIntegrationByParts : PointwiseIntegrationByParts
  ConjugationIdentity : ConjugationIdentity
  PlaneWaveLetterIdentities : PlaneWaveLetterIdentities
  slices : slices Cs
  slicesOrb : slicesOrb Cs
  smooth : smooth CB
  lettersExist : lettersExist
  germ : germ Cg₁ Cg₂

structure ClassicalAnalysisAndRepresentationTheorems : Prop where
  capEig : UnitaryLevelOperators.stCapEig
  markov : UnitaryLevelOperators.stMarkov
  herglotz : UnitaryLevelOperators.stHerglotz
  poisson : UnitaryLevelOperators.stPoisson
  statPhase : UnitaryLevelOperators.stStatPhase
  besselModel_unique : UnitaryLevelOperators.stJSZ
  qAnti : UnitaryLevelOperators.stQ_anti
  qBranch : UnitaryLevelOperators.stQ_branch
  qWigner : UnitaryLevelOperators.stQ_wigner
  tensorDS : ∀ D, OnePlaceEstimates.adm18 D
  tensorDSd : ∀ D, OnePlaceEstimates.DualTranslationPrinciple D
  kTypes : ∀ D, OnePlaceEstimates.adm20 D

end GroupS1

section GroupS5

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.UnitaryVolumeMass Formalism.MainNotions.S.Bridge

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def SW (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∃ C, OwnEv Fm fun C' Cl x i => ∀ u u', stSW (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A C

def Form (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => ∀ u u', stForm (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A

def TcritLow (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => stTcritLow (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0

def PTsum (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∃ C, ∀ Cn, OwnEv Fm fun C' Cl x i => stPTsum (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C

def PTDl (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∃ C, ∀ Cn, OwnEv Fm fun C' Cl x i => stPTDl (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C

def PieriNormsFamily (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∀ Cn, OwnEv Fm fun C' Cl x i => PieriNormDegreeFormula (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1

def Schur (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∃ C, OwnEv Fm fun C' Cl x i => stSchur (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 C1 C

def HH (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∃ C, OwnEv Fm fun C' Cl x i => ∀ u u', stHH (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A C

def Vol (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
    (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
      LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1) (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∃ C, OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u',
    stVol (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1 (Y x hx i u u') C' Cl Cg cb Cu cT CT C0 A C

def EpsT (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  ∀ δ > 0, OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 →
    Real.exp (((Fm.D x i).R.f : ℝ) * (2 : ℝ) ^ ((3 : ℝ) - (Fm.D x i).R.k)) - 1 ≤ δ

def AmpBessel (Cg cb Cu cT CT C0 C1 Ca : ℝ) : Prop :=
  ∀ Cn, OwnEv Fm fun C' Cl x i => AmpIsBessel (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 Ca

def Frames (Ch Cf : ℝ) : Prop := ∀ Cn, ∃ Cs₀, ∀ Cs ≥ Cs₀, ∀ x (i : Fm.Ix x), FrameChange (Fm.D x i) Ch Cs Cn Cf

def StdHypS (Cg cb Cu cT CT C0 Ch Cβ : ℝ) : Prop :=
  ∀ Cs Cs', OwnEv Fm fun C' Cl x i => StdOfHyp (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Ch Cs Cs' Cβ

def TFrame (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 →
    ∀ w, 1 ≤ Tr (Fm.D x i) w * kaS (Fm.D x i) ^ (2 * (Fm.D x i).R.rS)

def Mom : Prop :=
  ∀ Cg cb Cu cT CT C0 : ℝ, ∀ Cn, OwnEv Fm fun C' Cl x i => MomNormR (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn

def SHaar : Prop := ∀ x (i : Fm.Ix x), MuSHaar (Fm.D x i)

def Range (Cg cb Cu cT CT C0 Cs Cq0 Cr : ℝ) : Prop :=
  ∀ Cn Cq, OwnEv Fm fun C' Cl x i => RangeOfHyp (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cs Cn Cq Cq0 Cr

def DegSteps (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∀ Cn, OwnEv Fm fun C' Cl x i => DegStep (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1

def PieriProductBound (Cg cb Cu cT CT C0 C : ℝ) : Prop :=
  ∀ Cn, OwnEv Fm fun C' Cl x i => ProdBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C

end GroupS5

end Formalism.MainNotions.PX

end
