import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AePolynomialNonvanishingRows
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ae_polynomial_nonvanishing_rows : ∀ (n e δ : ℕ) (h : HermNorm n) (q : MvPolynomial (Fin e × Fin n) ℂ), q ≠ 0 → IsMultiHomog δ q →
  ∀ᵐ π : Fin (e + 1) → Fin n → ℂ, eval (nrmGroups h e (coefRows h π)) q ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.ae_eval_nrmGroups_coefRows_ne_zero | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.ae_eval_nrmGroups_coefRows_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.ae_eval_nrmGroups_coefRows_ne_zero <;> assumption)
