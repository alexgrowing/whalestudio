import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialCoefficientComparison
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TZero
open Finset GlobalTheory.CompanionTheory.CoefId
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomial_coefficient_comparison : ∀ {n : ℕ} {ι κ : Type} (I : Finset ι) (J : Finset κ) (f : ι → ℂ) (g : κ → ℂ) (e : ι → Fin n → ℤ) (e' : κ → Fin n → ℤ), (∀ z : Fin n → ℂ, (∀ a, ‖z a‖ = 1) → Function.Injective (fun a => z a ^ 2) → ∑ i ∈ I, f i * mon (e i) z = ∑ j ∈ J, g j * mon (e' j) z) → ∀ m : Fin n → ℤ, ∑ i ∈ I.filter (fun i => e i = m), f i = ∑ j ∈ J.filter (fun j => e' j = m), g j := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.laurent_indep_torus | exact GlobalTheory.CompanionTheory.CoefId.laurent_indep_torus | (intros; apply GlobalTheory.CompanionTheory.CoefId.laurent_indep_torus <;> assumption)
