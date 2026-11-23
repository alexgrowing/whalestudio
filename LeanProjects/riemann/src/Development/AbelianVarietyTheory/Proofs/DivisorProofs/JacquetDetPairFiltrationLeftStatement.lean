import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetDetPairFiltrationLeft
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
open GlobalTheory.PRep GlobalTheory.SmGL Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_det_pair_filtration_left : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.GeometricLemmaFiltration → ∀ (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → ∀ (u v : ℕ) (e : Fin 1 ⊕ Fin (u + v) ≃ Fin (u + 1 + v)) (ϖ : kˣ), ∃ (N : ℕ) (S : Fin (N + 1) → Subrepresentation (jac₂ e (prod₂ (detRep (Fin (u + 1)) χ₁) (detRep (Fin v) χ₂)))), Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last N) = ⊤ ∧ ∃ t₀ : Fin N, Nonempty ((subQuot (S t₀.succ) (S t₀.castSucc)).Equiv (extTensor (detRep (Fin 1) (χ₁ * absPow k (-(u : ℂ) / 2))) (prod₂ (detRep (Fin u) (χ₁ * absPow k (1 / 2))) (detRep (Fin v) χ₂)))) ∧ ∀ t, t ≠ t₀ → ∀ w ∈ (S t.succ).toSubmodule, jac₂ e (prod₂ (detRep (Fin (u + 1)) χ₁) (detRep (Fin v) χ₂)) (GeneralLinearGroup.scalar (Fin 1) ϖ, 1) w - (((χ₂ * absPow k ((1 - (v : ℂ)) / 2)) ϖ : ℂˣ) : ℂ) • w ∈ (S t.castSucc).toSubmodule := by
  first | exact @GlobalTheory.DetProdCells.jac_prod_det_filtration | exact GlobalTheory.DetProdCells.jac_prod_det_filtration | (intros; apply GlobalTheory.DetProdCells.jac_prod_det_filtration <;> assumption)
