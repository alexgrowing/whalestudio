import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerContractionChartForms
open GlobalTheory GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.euler_contraction_chart_forms : ∀ (K : Type) [Field K] (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (i : Fin n) (θ : abelian₂ K →ₗ[K] abelian₂ K), (∀ j, (x j : K) ∈ A) → IsEulerContraction x i θ → (∀ q, ∀ η ∈ chartForms A x J t (q + 1), θ η ∈ chartForms A x J t q) ∧ ∀ η ∈ chartForms A x J t 0, θ η = 0 := by
  first | exact @_root_.GlobalTheory.LogDR.chartForms_stable_euler | exact _root_.GlobalTheory.LogDR.chartForms_stable_euler | (intros; apply _root_.GlobalTheory.LogDR.chartForms_stable_euler <;> assumption)
