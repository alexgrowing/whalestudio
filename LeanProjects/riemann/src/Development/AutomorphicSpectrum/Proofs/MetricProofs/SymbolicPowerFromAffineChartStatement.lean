import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SymbolicPowerFromAffineChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symbolic_power_from_affine_chart : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (f s : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) (n : ℕ), IsMultiHomogIdeal P → IsMultiHomogIdeal Q → Q.IsPrime → (∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) → IsMultiHomog f a → s ∉ Q → s * f ∈ Q ^ n ⊔ P → ∃ s' ∉ SncRes.ideal Q p, s' * bind₁ (SncRes.lift p) f ∈ SncRes.ideal Q p ^ n ⊔ SncRes.ideal P p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom.relation_dehom | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom.relation_dehom | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom.relation_dehom <;> assumption)
