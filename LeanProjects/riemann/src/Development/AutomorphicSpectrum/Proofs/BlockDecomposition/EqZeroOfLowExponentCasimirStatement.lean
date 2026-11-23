import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfLowExponentCasimir
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqZeroOfMem
open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_low_exponent_casimir : ∀ {n : ℕ} (m : Fin n × Fin n →₀ ℕ), LowExp m → (∀ i j : Fin n, (j : ℕ) = i + 1 → ∃ p : ℕ, 1 + wt m i - wt m j = (p : ℤ)) → casC (fun k => rhoVec n k + (wt m k : ℂ)) = casC (rhoVec n) → m = 0 := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.NormIneq.eq_zero_of_casC_eq | exact GlobalTheory.CompanionTheory.PresRho.NormIneq.eq_zero_of_casC_eq | (intros; apply GlobalTheory.CompanionTheory.PresRho.NormIneq.eq_zero_of_casC_eq <;> assumption)
