import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanAutomorphismConjugatesOfNumberFieldIndepende

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_automorphismConjugates_of_numberField_independent_eq_top : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (ι : Type) [Fintype ι] (e : ι → ℂ), (∀ c : ι → K, ∑ i, σ (c i) * e i = 0 → c = 0) → Submodule.span ℂ {v : ι → ℂ | ∃ φ : ℂ ≃+* ℂ, (∀ x, φ (σ x) = σ x) ∧ v = fun i => φ (e i)} = ⊤ := by
  first | exact @GlobalTheory.ConjSpan.span_conj_eq_top | exact GlobalTheory.ConjSpan.span_conj_eq_top | (intros; apply GlobalTheory.ConjSpan.span_conj_eq_top <;> assumption)
