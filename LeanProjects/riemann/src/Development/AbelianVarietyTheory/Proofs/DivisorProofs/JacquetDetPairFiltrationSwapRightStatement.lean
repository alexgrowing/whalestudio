import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetDetPairFiltrationSwapRight
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
open GlobalTheory.PRep GlobalTheory.SmGL Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_det_pair_filtration_swap_right : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.GeometricLemmaFiltration → ∀ (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → ∀ (u v : ℕ) (e : Fin (u + v) ⊕ Fin 1 ≃ Fin (u + (v + 1))) (ϖ : kˣ), ∃ (N : ℕ) (S : Fin (N + 1) → Subrepresentation (jac₂ e (prod₂ (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)))), Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last N) = ⊤ ∧ ∃ t₀ : Fin N, Nonempty ((subQuot (S t₀.succ) (S t₀.castSucc)).Equiv (extTensor (prod₂ (detRep (Fin u) χ₁) (detRep (Fin v) (χ₂ * absPow k (-(1 / 2))))) (detRep (Fin 1) (χ₂ * absPow k ((v : ℂ) / 2))))) ∧ ∀ t, t ≠ t₀ → ∀ w ∈ (S t.succ).toSubmodule, jac₂ e (prod₂ (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)) (1, GeneralLinearGroup.scalar (Fin 1) ϖ) w - (((χ₁ * absPow k (((u : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ) • w ∈ (S t.castSucc).toSubmodule := by
  first | exact @GlobalTheory.CellRS.main | exact GlobalTheory.CellRS.main | (intros; apply GlobalTheory.CellRS.main <;> assumption)
