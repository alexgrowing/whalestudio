import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicTemperedDistPoisson
import Mathlib
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_tempered_dist_poisson : ∀ (n : ℕ) (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ),
    (∀ k : Fin n → ℤ, ∀ f f' : SchwartzMap (Fin n → ℝ) ℂ, (∀ x, f' x = f (x + fun i => (k i : ℝ))) → T f' = T f) →
    (∀ m : Fin n → ℤ, ∀ f f' : SchwartzMap (Fin n → ℝ) ℂ,
      (∀ x, f' x = Complex.exp (2 * Real.pi * Complex.I * ((∑ i, (m i : ℝ) * x i : ℝ) : ℂ)) * f x) → T f' = T f) →
    ∃ c : ℂ, ∀ f : SchwartzMap (Fin n → ℝ) ℂ, T f = c * ∑' k : Fin n → ℤ, f (fun i => (k i : ℝ)) := by
  first | exact @GlobalTheory.IntComb.dirac_comb_unique | exact GlobalTheory.IntComb.dirac_comb_unique | (intros; apply GlobalTheory.IntComb.dirac_comb_unique <;> assumption)
