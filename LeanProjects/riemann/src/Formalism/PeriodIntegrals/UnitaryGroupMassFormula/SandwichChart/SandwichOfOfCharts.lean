import Mathlib
import Formalism.PeriodIntegrals.LongWeylElementSquare
import Formalism.PeriodIntegrals.SwSand

noncomputable section

open Matrix Filter Topology Classical
open scoped ENNReal NNReal

namespace PI.SwSandwichOfWork

open PI.SwBig PI.SwSand

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

def NormRL : Prop := ∀ (k r : ℕ) (X : Mat k r), ‖RL X‖ = ‖X‖

def LogG : Prop := ∀ k r : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ L : Mat k r, ‖L‖ < δ →
  NormedSpace.exp L ∈ UH (Hpk k r) → L ∈ uH k r

def ChartFwd : Prop := ∀ (k r : ℕ) (η : ℝ), 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ Vs k r, ‖v‖ < δ →
  ∃ Y ∈ uH k r, NormedSpace.exp Y = Phi k r v.1 v.2.1 v.2.2.1 v.2.2.2 ∧ ‖Y‖ ≤ (1 + η) * ‖Lm k r v‖

def ChartBwd : Prop := ∀ (k r : ℕ) (η : ℝ), 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ Y ∈ uH k r, ‖Y‖ < δ →
  ∃ v ∈ Vs k r, Phi k r v.1 v.2.1 v.2.2.1 v.2.2.2 = NormedSpace.exp Y ∧ ‖v‖ < η ∧
    (1 - η) * ‖Lm k r v‖ ≤ ‖Y‖

def ChartFwdOf : Prop :=
  NormRL → LogG → LongWeylElementSquare → BigCellG → PhiForm → PhiDeriv → LieWb → ExpN → LIso → ChartFwd

def ChartBwdOf : Prop :=
  NormRL → LogG → LongWeylElementSquare → BigCellG → PhiForm → PhiDeriv → LieWb → ExpN → LIso → ChartBwd

def SideB : Prop :=
  NormRL → LieG → LieWb → PhiForm → LieEN → LIso → ChartFwd →
  ∀ (k r : ℕ) (ε : ℝ), 0 < ε → ε < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < δ →
    ∀ (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r), Matrix.of n ∈ Nset k r → Matrix.of m ∈ UWb k r →
      Matrix.of n' ∈ Nset k r →
      Qf k r n c m n' < ENNReal.ofReal (((1 - ε) * ρ) ^ 2) → Psi k r n c m n' ∈ gBall k r ρ

def SideA : Prop :=
  NormRL → LieG → LieWb → GaussUniq → PhiForm → LongWeylElementSquare → LieEN → ExpN → LIso → ChartBwd →
  ∀ (k r : ℕ) (ε : ℝ), 0 < ε → ε < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < δ →
    ∀ (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r), Matrix.of n ∈ Nset k r → Matrix.of m ∈ UWb k r →
      Matrix.of n' ∈ Nset k r →
      Psi k r n c m n' ∈ gBall k r ρ → Qf k r n c m n' < ENNReal.ofReal (((1 + ε) * ρ) ^ 2)

theorem sandwichOf_of_charts (h0 : NormRL) (h1 : LogG) (h2 : ChartFwdOf) (h3 : ChartBwdOf)
    (h4 : SideB) (h5 : SideA) : SandwichOf := by
  intro hLieG hLieWb hGauss hPhiForm hBig hPhiDeriv hLIso hW0 hLieEN hExpN
  have hF : ChartFwd := h2 h0 h1 hW0 hBig hPhiForm hPhiDeriv hLieWb hExpN hLIso
  have hB : ChartBwd := h3 h0 h1 hW0 hBig hPhiForm hPhiDeriv hLieWb hExpN hLIso
  intro k r ε hε hε1
  obtain ⟨δ₁, hδ₁, hB'⟩ := h4 h0 hLieG hLieWb hPhiForm hLieEN hLIso hF k r ε hε hε1
  obtain ⟨δ₂, hδ₂, hA'⟩ := h5 h0 hLieG hLieWb hGauss hPhiForm hW0 hLieEN hExpN hLIso hB k r ε hε hε1
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro ρ hρ hρδ n c m n' hn hm hn'
  exact ⟨hA' ρ hρ (lt_of_lt_of_le hρδ (min_le_right _ _)) n c m n' hn hm hn',
    hB' ρ hρ (lt_of_lt_of_le hρδ (min_le_left _ _)) n c m n' hn hm hn'⟩

end PI.SwSandwichOfWork
