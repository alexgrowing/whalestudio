import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.DensityAveraging

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

section defs

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def nzMin (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) : ℕ :=
  (Finset.univ.filter fun l : Fin (r + 2) => Dmin k r D.z D.z' γ l ≠ 0).card

def VanAt (D : B.RealPlaceData k r Wp Wq) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) : Prop :=
  ∀ O : OrbData D γ, O.J F' = 0

def DensHyp (CV : ℕ) (D : B.RealPlaceData k r Wp Wq) (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  1 ≤ r ∧ 0 < ε ∧ (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A ∧ mmV CV r ≤ mm ∧ B.InCC A mm F' ∧
    (∀ g ∈ B.GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) ∧ (∀ g ∈ bigPos D, B.JF D F' g = 0)

def CaseJ (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) : Prop :=
  ∃ l j : Fin (r + 2), l < j ∧ j ≠ Fin.last (r + 1) ∧ Dmin k r D.z D.z' γ l = 0 ∧ Dmin k r D.z D.z' γ j ≠ 0

def CaseTop (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) : Prop :=
  (∃ l : Fin (r + 2), Dmin k r D.z D.z' γ l = 0) ∧ ¬ CaseJ D γ

def MoreBlocks (D : B.RealPlaceData k r Wp Wq) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) : Prop :=
  ∀ γ' : B.Mat k r, IsRelevant D γ' → 0 < Gf k r D.z D.z' γ' → nzMin D γ < nzMin D γ' → VanAt D F' γ'

end defs

def DensBig : Prop :=
  ∃ CV₀ : ℕ, ∀ CV : ℕ, CV₀ ≤ CV → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r),
    DensHyp CV D A ε mm F' → γ ∈ bigPos D → IsRelevant D γ → VanAt D F' γ

def DensStepJ : Prop :=
  ∃ CV₀ : ℕ, ∀ CV : ℕ, CV₀ ≤ CV → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r),
    DensHyp CV D A ε mm F' → IsRelevant D γ → 0 < Gf k r D.z D.z' γ → CaseJ D γ → MoreBlocks D F' γ →
      VanAt D F' γ

def DensStepTop : Prop :=
  ∃ CV₀ : ℕ, ∀ CV : ℕ, CV₀ ≤ CV → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r),
    DensHyp CV D A ε mm F' → IsRelevant D γ → 0 < Gf k r D.z D.z' γ → CaseTop D γ → MoreBlocks D F' γ →
      VanAt D F' γ

def LemmaDensOfSteps : Prop := DensBig → DensStepJ → DensStepTop → LemmaDens

def RTrivBig : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r), γ ∈ bigPos D → IsRelevant D γ → Rset γ = {1}

def DensBigOfParts : Prop := RTrivBig → DensBig

section avg

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

structure AvgDatum (D : B.RealPlaceData k r Wp Wq) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) where
  V : Type
  [instG : AddCommGroup V]
  [instM : Module ℂ V]
  p : Seminorm ℂ V
  β : ℂ
  β_ne : β ≠ 0
  s : ℕ
  w : Fin s → ℂ
  w_inj : Function.Injective w
  a : Fin s → V
  k₀ : Fin s
  tie : p (a k₀) = 0 → VanAt D F' γ

attribute [instance] AvgDatum.instG AvgDatum.instM

def AvgDatum.GermBound {D : B.RealPlaceData k r Wp Wq} {F' : B.Mat k r → (Wq →L[ℂ] Wp)} {γ : B.Mat k r}
    (S : AvgDatum D F' γ) : Prop :=
  ∃ C' x₁ : ℝ, ∀ x : ℂ, x₁ ≤ ‖x‖ → S.p (∑ j, G.psi S.β (S.w j * x) • S.a j) ≤ C' / ‖x‖

end avg

def AvgInputJ : Prop :=
  ∃ CV₀ : ℕ, ∀ CV : ℕ, CV₀ ≤ CV → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r),
    DensHyp CV D A ε mm F' → IsRelevant D γ → 0 < Gf k r D.z D.z' γ → CaseJ D γ →
      ∃ S : AvgDatum D F' γ, MoreBlocks D F' γ → S.GermBound

def AvgInputTop : Prop :=
  ∃ CV₀ : ℕ, ∀ CV : ℕ, CV₀ ≤ CV → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r),
    DensHyp CV D A ε mm F' → IsRelevant D γ → 0 < Gf k r D.z D.z' γ → CaseTop D γ →
      ∃ S : AvgDatum D F' γ, MoreBlocks D F' γ → S.GermBound

def DensStepJOfAvg : Prop := AvgInputJ → AveragingZero → DensStepJ

def DensStepTopOfAvg : Prop := AvgInputTop → AveragingZero → DensStepTop

def RTrivBigOfParts : Prop := C2.C1ii → C2.CurvatureConditionOneClauseThree → RTrivBig

end Formalism.FourierDecayAlt.DensityAveraging
