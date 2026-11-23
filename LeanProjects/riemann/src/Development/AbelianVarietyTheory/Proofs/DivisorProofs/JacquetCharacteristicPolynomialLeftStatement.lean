import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetCharacteristicPolynomialLeft
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
open GlobalTheory.PRep GlobalTheory.SmGL Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_characteristic_polynomial_left : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.GeometricLemmaFiltration → ∀ (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → ∀ (u v : ℕ) (m : Type) [Fintype m] [DecidableEq m] (e : Fin 1 ⊕ m ≃ Fin (u + v)) (ϖ : kˣ), Polynomial.aeval (jac₂ e (prod₂ (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)) (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)) ((Polynomial.X - Polynomial.C (((χ₁ * absPow k ((1 - (u : ℂ)) / 2)) ϖ : ℂˣ) : ℂ)) * (Polynomial.X - Polynomial.C (((χ₂ * absPow k ((1 - (v : ℂ)) / 2)) ϖ : ℂˣ) : ℂ))) = 0 := by
  first | exact @GlobalTheory.ScalLeft.aeval_jac₂_scalar_eq_zero | exact GlobalTheory.ScalLeft.aeval_jac₂_scalar_eq_zero | (intros; apply GlobalTheory.ScalLeft.aeval_jac₂_scalar_eq_zero <;> assumption)
