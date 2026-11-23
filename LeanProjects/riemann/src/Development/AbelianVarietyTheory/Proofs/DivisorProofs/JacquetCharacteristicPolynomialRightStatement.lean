import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetCharacteristicPolynomialRight
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
open GlobalTheory.PRep GlobalTheory.SmGL Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_characteristic_polynomial_right : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.GeometricLemmaFiltration → ∀ (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → ∀ (u v : ℕ) (m : Type) [Fintype m] [DecidableEq m] (e : m ⊕ Fin 1 ≃ Fin (u + v)) (ϖ : kˣ), Polynomial.aeval (jac₂ e (prod₂ (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)) (1, GeneralLinearGroup.scalar (Fin 1) ϖ)) ((Polynomial.X - Polynomial.C (((χ₁ * absPow k (((u : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ)) * (Polynomial.X - Polynomial.C (((χ₂ * absPow k (((v : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ))) = 0 := by
  first | exact @GlobalTheory.ScalRight.scal_right | exact GlobalTheory.ScalRight.scal_right | (intros; apply GlobalTheory.ScalRight.scal_right <;> assumption)
