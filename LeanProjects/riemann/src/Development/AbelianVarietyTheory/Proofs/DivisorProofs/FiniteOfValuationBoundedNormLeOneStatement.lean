import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfValuationBoundedNormLeOne
import Mathlib
open NumberField IsDedekindDomain Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_of_valuation_bounded_norm_le_one : ∀ (E : Type) [Field E] [NumberField E] (X : Set E), (∀ w : HeightOneSpectrum (𝓞 E), ∃ N : ℤ, ∀ a ∈ X, w.valuation E a ≤ WithZero.exp N) → (∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ a ∈ X, w.valuation E a ≤ 1) → (∀ a ∈ X, ∀ τ : E →+* ℂ, ‖τ a‖ ≤ 1) → X.Finite := by
  first | exact @GlobalTheory.BCT.SuppFin.finite_of_valuation_bounded_of_norm_le_one | exact GlobalTheory.BCT.SuppFin.finite_of_valuation_bounded_of_norm_le_one | (intros; apply GlobalTheory.BCT.SuppFin.finite_of_valuation_bounded_of_norm_le_one <;> assumption)
