import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionTransitionPolynomial
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_resolution_transition_polynomial : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)), ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P → (∀ p : (k : K) → ι k, SncRes.coord P p '' SncRes.src P p = {t | ∀ h ∈ SncRes.ideal P p, eval t h = 0}) ∧ ∀ p p' : (k : K) → ι k, ∀ x ∈ SncRes.src P p ∩ SncRes.src P p', ∃ (q : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (F : Fin (Fintype.card (Σ k, ι k)) → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ), eval (SncRes.coord P p x) q ≠ 0 ∧ ∀ y ∈ SncRes.src P p ∩ SncRes.src P p', eval (SncRes.coord P p y) q ≠ 0 → ∀ l, SncRes.coord P p' y l * eval (SncRes.coord P p y) q = eval (SncRes.coord P p y) (F l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_image_and_trans | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_image_and_trans | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_image_and_trans <;> assumption)
