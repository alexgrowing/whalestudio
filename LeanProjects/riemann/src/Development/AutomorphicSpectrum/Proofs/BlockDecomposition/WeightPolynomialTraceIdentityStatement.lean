import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightPolynomialTraceIdentity
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CPoly
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCount.Tope
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_polynomial_trace_identity : ∀ {n : ℕ} (lam : Fin n → ℤ) (E : KMod n) (T : E.V →L[ℂ] E.V), IsLefK lam E T →
    (⨆ μ, wtDual E μ) = ⊤ → iSupIndep (wtDual E) → ∀ s : Finset (Fin n → ℤ), (∀ μ, wtDual E μ ≠ ⊥ → μ ∈ s) →
      cPoly s (fun μ => trOn (wtDual E μ) (dualT E 1 : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ))) * altL (delZ n) ^ 2 =
          pPL n * altL (lam + delZ n) ^ 2 ∧
        cPoly s (fun μ => trOn (wtDual E μ) (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ))) * frL n (altL (delZ n)) =
          pPL n * frL n (altL (lam + delZ n)) := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.Tope.Ident.lefK_laurent_ident | exact GlobalTheory.CompanionTheory.RealCount.Tope.Ident.lefK_laurent_ident | (intros; apply GlobalTheory.CompanionTheory.RealCount.Tope.Ident.lefK_laurent_ident <;> assumption)
