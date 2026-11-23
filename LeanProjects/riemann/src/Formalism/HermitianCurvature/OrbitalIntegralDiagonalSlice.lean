import Formalism.HermitianCurvature.LemmaDensOfSteps

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.OrbitalSlices

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6 Formalism.FourierDecayAlt.DensityAveraging

section defs

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

structure SlicePt (D : B.RealPlaceData k r Wp Wq) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) where
  m : ℕ
  β : ℂ
  β_ne : β ≠ 0
  Dd : ℂ
  Dd_ne : Dd ≠ 0
  z₀ : ℂ
  z₀_pow : z₀ ^ (m + 2) = (-1) ^ (m + 3) * Dd
  Ψ : G.Mat (m + 1 + 1) → (Wq →L[ℂ] Wp)
  pt : ℂ → ℂ → B.Mat k r
  δ : ℝ
  δ_pos : 0 < δ

variable {D : B.RealPlaceData k r Wp Wq} {F' : B.Mat k r → (Wq →L[ℂ] Wp)} {γ : B.Mat k r}

def SlicePt.OrbitalIntegralLongElement (S : SlicePt D F' γ) : Prop :=
  ∀ O : OrbData D γ, O.J F' = G.OmLong S.β (S.m + 1) S.Ψ S.z₀

def SlicePt.OrbitalIntegralDiagonalSlice (S : SlicePt D F' γ) : Prop :=
  ∀ t c : ℂ, t ≠ 0 → ‖t‖ < S.δ → c * t ^ (S.m + 1) = S.Dd →
    ∃ O : OrbData D (S.pt t c), O.J F' = G.OmBlock S.β (S.m + 1) S.Ψ t c

def SlicePt.DiagRel (S : SlicePt D F' γ) : Prop :=
  ∀ t c : ℂ, t ≠ 0 → ‖t‖ < S.δ → c * t ^ (S.m + 1) = S.Dd →
    IsRelevant D (S.pt t c) ∧ 0 < Gf k r D.z D.z' (S.pt t c) ∧ nzMin D γ < nzMin D (S.pt t c)

def SlicePt.Decay (S : SlicePt D F' γ) (A K : ℝ) (kk : ℕ) : Prop :=
  G.DerivBound kk (G.detSet (S.m + 1) {S.Dd}) (fun Z => K * min 1 (‖Z‖ ^ (-A))) S.Ψ

def SlicePt.Good (S : SlicePt D F' γ) (C₁ C₂ : ℕ) : Prop :=
  ∃ (A K : ℝ) (kk : ℕ), (C₁ : ℝ) * ((S.m : ℝ) + 2) ^ 2 ≤ A ∧ C₂ * (S.m + 2) ^ 2 ≤ kk ∧ S.Decay A K kk ∧
    S.OrbitalIntegralLongElement ∧ S.OrbitalIntegralDiagonalSlice ∧ S.DiagRel

end defs

def SliceInputJ : Prop :=
  ∀ C₁ C₂ : ℕ, ∃ CV₀ : ℕ, ∀ CV : ℕ, CV₀ ≤ CV → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp))
    (γ : B.Mat k r),
    DensHyp CV D A ε mm F' → IsRelevant D γ → 0 < Gf k r D.z D.z' γ → CaseJ D γ →
      ∃ S : SlicePt D F' γ, S.Good C₁ C₂

def SliceInputTop : Prop :=
  ∀ C₁ C₂ : ℕ, ∃ CV₀ : ℕ, ∀ CV : ℕ, CV₀ ≤ CV → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp))
    (γ : B.Mat k r),
    DensHyp CV D A ε mm F' → IsRelevant D γ → 0 < Gf k r D.z D.z' γ → CaseTop D γ →
      ∃ S : SlicePt D F' γ, S.Good C₁ C₂

def AvgInputJOfSlice : Prop := G.GermRate → SliceInputJ → AvgInputJ

def AvgInputTopOfSlice : Prop := G.GermRate → SliceInputTop → AvgInputTop

end Formalism.FourierDecayAlt.OrbitalSlices
