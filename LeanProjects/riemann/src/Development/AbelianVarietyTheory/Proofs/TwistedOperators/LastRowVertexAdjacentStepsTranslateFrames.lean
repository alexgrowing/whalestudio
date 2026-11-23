import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnfSupportOfNeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiStepLeftChangeMeasurePreservingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepPointMulPeriodUnipotentGLMeasurePreservingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPhaseAdjacentStepsInvariantVertexStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport

namespace GlobalTheory.FlatStepVertex

theorem mul_reindex_gen {k : Type} [Field k] {a c b : ℕ} {ι' ι : Type} (h : a + c = b) (f : ι' ≃ ι) (g : GL (Fin b) k)
    (D : Matrix (Fin a ⊕ Fin c) ι' k) :
    g.val * D.reindex (frame h) f = ((frameGL h g).val * D).reindex (frame h) f := by
  ext i j
  simp only [reindex_apply, submatrix_apply, mul_apply, frameGL_val]
  exact (Fintype.sum_equiv (frame h) _ _ (fun x => by simp)).symm

theorem reindex_mul_gen {k : Type} [Field k] {a c b : ℕ} {ι' ι : Type} (h : a + c = b) (f : ι' ≃ ι) (g : GL (Fin b) k)
    (D : Matrix ι' (Fin a ⊕ Fin c) k) :
    D.reindex f (frame h) * g.val = (D * (frameGL h g).val).reindex f (frame h) := by
  ext i j
  simp only [reindex_apply, submatrix_apply, mul_apply, frameGL_val]
  exact (Fintype.sum_equiv (frame h) _ _ (fun x => by simp)).symm

end GlobalTheory.FlatStepVertex

theorem GlobalTheory.flatStep_vertex : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {a₀ a₁ a₂ b c c₀ c' : ℕ} (ν : Measure k) [ν.IsAddHaarMeasure] (hc₀ : c₀ = c + 1) (hc' : c' = c + 1)
    (h₁ : a₁ + c₀ = b) (h₂ : a₁ + (c + 1) = b) (h' : a₁ + c' = b) (g : GL (Fin b) k) (κ : GL (Fin a₁) k),
    valuation k (gdet κ : k) = 1 → ∀ v ∈ symN k (Fin a₁) c', frameGL h' g = v * embX c' κ →
    ∀ (x₀ : Matrix (Fin a₁) (Fin a₀) k) (x₁ : Matrix (Fin a₂) (Fin a₁) k),
    ∃ φ₀ : (StepVar (Fin a₁) c₀ (Fin a₀) → k) ≃ᵐ (StepVar (Fin a₁) c₀ (Fin a₀) → k),
      MeasurePreserving φ₀ (stepVol ν (Fin a₁) c₀ (Fin a₀)) (stepVol ν (Fin a₁) c₀ (Fin a₀)) ∧
    ∃ φ₁ : (StepVar (Fin a₂) c (Fin a₁) → k) ≃ᵐ (StepVar (Fin a₂) c (Fin a₁) → k),
      MeasurePreserving φ₁ (stepVol ν (Fin a₂) c (Fin a₁)) (stepVol ν (Fin a₂) c (Fin a₁)) ∧
    ∀ e₀ e₁,
      (∀ {ι : Type} (f : Fin a₀ ⊕ Fin (c₀ + 1) ≃ ι), (g⁻¹).val * (stepPt x₀ e₀).reindex (frame h₁) f =
        (stepPt ((κ⁻¹).val * x₀) (φ₀ e₀)).reindex (frame h₁) f) ∧
      (∀ {ι : Type} (f : Fin a₂ ⊕ Fin c ≃ ι), (stepPt x₁ e₁).reindex f (frame h₂) * g.val =
        (stepPt (x₁ * κ.val) (φ₁ e₁)).reindex f (frame h₂)) ∧
      (ch (stepPt ((κ⁻¹).val * x₀) (φ₀ e₀)) + ch (stepPt (x₁ * κ.val) (φ₁ e₁)) + (if Even c₀ then ∑ r : Fin a₁,
          (∑ l : Fin c, if l.val = c / 2 then stepPt (x₁ * κ.val) (φ₁ e₁) (.inr l) (.inl r) else 0) *
            stepPt ((κ⁻¹).val * x₀) (φ₀ e₀) (.inl r) (.inr ⟨c₀ / 2, by omega⟩) else 0) =
        ch (stepPt x₀ e₀) + ch (stepPt x₁ e₁) + (if Even c₀ then ∑ r : Fin a₁,
          (∑ l : Fin c, if l.val = c / 2 then stepPt x₁ e₁ (.inr l) (.inl r) else 0) *
            stepPt x₀ e₀ (.inl r) (.inr ⟨c₀ / 2, by omega⟩) else 0)) ∧
      (Odd c₀ → ∀ (l : Fin c₀) (s : Fin a₀), l.val = c₀ / 2 →
        stepPt ((κ⁻¹).val * x₀) (φ₀ e₀) (.inr l) (.inl s) = stepPt x₀ e₀ (.inr l) (.inl s)) ∧
      (Odd c₀ → ∀ (r : Fin a₂) (i : Fin (c + 1)), i.val = c / 2 →
        stepPt (x₁ * κ.val) (φ₁ e₁) (.inl r) (.inr i) = stepPt x₁ e₁ (.inl r) (.inr i)) := by
  intro k _ _ _ _ _ _ a₀ a₁ a₂ b c c₀ c' ν _ hc₀ hc' h₁ h₂ h' g κ hκ v hv hg x₀ x₁
  subst hc₀ hc'
  obtain ⟨φ₀, hφ₀, H₀⟩ := GlobalTheory.T.fourierJacobiStep_leftChange_measurePreserving (n := Fin a₁) (n' := Fin a₀) (c := c + 1) ν v hv κ hκ x₀
  obtain ⟨φ₁, hφ₁, H₁⟩ := GlobalTheory.T.stepPoint_mul_periodUnipotent_GL_measurePreserving (n := Fin a₂) (n' := Fin a₁) (c := c) ν v hv κ hκ x₁
  refine ⟨φ₀, hφ₀, φ₁, hφ₁, fun e₀ e₁ => ?_⟩
  have hg₁ : frameGL h₁ g = v * embX (c + 1) κ := hg
  have hg₂ : frameGL h₂ g = v * embX (c + 1) κ := hg
  obtain ⟨A, B⟩ := GlobalTheory.T.fourierJacobiPhase_adjacentSteps_invariant_vertex (n₀ := Fin a₀) (n := Fin a₁) (n₂ := Fin a₂) (c := c) v hv κ x₀ e₀ x₁ e₁
    (stepPt ((κ⁻¹).val * x₀) (φ₀ e₀)) (stepPt (x₁ * κ.val) (φ₁ e₁)) (H₀ e₀).symm (H₁ e₁).symm
  refine ⟨fun f => ?_, fun f => ?_, A, fun ho l s hl => ?_, fun ho r i hi => ?_⟩
  · rw [GlobalTheory.FlatStepVertex.mul_reindex_gen, map_inv, hg₁, H₀]
  · rw [GlobalTheory.FlatStepVertex.reindex_mul_gen, hg₂, H₁]
  · rw [show l = ⟨(c + 1) / 2, by omega⟩ from Fin.ext hl]
    exact (B ho).1 s
  · rw [show i = ⟨c / 2, by omega⟩ from Fin.ext hi]
    exact (B ho).2 r
