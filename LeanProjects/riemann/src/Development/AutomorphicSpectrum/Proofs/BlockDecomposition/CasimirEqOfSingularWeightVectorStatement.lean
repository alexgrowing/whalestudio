import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirEqOfSingularWeightVector
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqZeroOfMem
open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_eq_of_singular_weight_vector : ∀ {n : ℕ} (μ : Fin n → ℤ) (x : U n), IsAdW μ x → (∀ a : Fin n × Fin n, IsUpper a → e a * x ∈ Jp n) → x ∉ Jp n → casC (fun k => rhoVec n k + (μ k : ℂ)) = casC (rhoVec n) := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.casC_rho_add_eq | exact GlobalTheory.CompanionTheory.PresRho.casC_rho_add_eq | (intros; apply GlobalTheory.CompanionTheory.PresRho.casC_rho_add_eq <;> assumption)
