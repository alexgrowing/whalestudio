import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPhaseAdjacentStepsInvariantVertex
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiPhase_adjacentSteps_invariant_vertex : ∀ {k : Type} [Field k] {n₀ n n₂ : Type} [Fintype n₀] [DecidableEq n₀] [Fintype n] [DecidableEq n] [Fintype n₂] [DecidableEq n₂] {c : ℕ},
    ∀ v ∈ symN k n (c + 1), ∀ (κ : GL n k) (x₀ : Matrix n n₀ k) (e₀ : StepVar n (c + 1) n₀ → k) (x₁ : Matrix n₂ n k) (e₁ : StepVar n₂ c n → k)
      (d₀ : Matrix (n ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k) (d₁ : Matrix (n₂ ⊕ Fin c) (n ⊕ Fin (c + 1)) k),
      d₀ = ((v * embX (c + 1) κ)⁻¹).val * stepPt x₀ e₀ → d₁ = stepPt x₁ e₁ * (v * embX (c + 1) κ).val →
      (ch d₀ + ch d₁ + (if Even (c + 1) then ∑ r : n, (∑ l : Fin c, if l.val = c / 2 then d₁ (.inr l) (.inl r) else 0) *
          d₀ (.inl r) (.inr ⟨(c + 1) / 2, by omega⟩) else 0) =
        ch (stepPt x₀ e₀) + ch (stepPt x₁ e₁) + (if Even (c + 1) then ∑ r : n,
          (∑ l : Fin c, if l.val = c / 2 then stepPt x₁ e₁ (.inr l) (.inl r) else 0) *
            stepPt x₀ e₀ (.inl r) (.inr ⟨(c + 1) / 2, by omega⟩) else 0)) ∧
      (Odd (c + 1) → (∀ s : n₀, d₀ (.inr ⟨(c + 1) / 2, by omega⟩) (.inl s) = stepPt x₀ e₀ (.inr ⟨(c + 1) / 2, by omega⟩) (.inl s)) ∧
        ∀ r : n₂, d₁ (.inl r) (.inr ⟨c / 2, by omega⟩) = stepPt x₁ e₁ (.inl r) (.inr ⟨c / 2, by omega⟩)) := by
  first | exact @GlobalTheory.PhaseStep.phase_step_inv | exact GlobalTheory.PhaseStep.phase_step_inv | (intros; apply GlobalTheory.PhaseStep.phase_step_inv <;> assumption)
