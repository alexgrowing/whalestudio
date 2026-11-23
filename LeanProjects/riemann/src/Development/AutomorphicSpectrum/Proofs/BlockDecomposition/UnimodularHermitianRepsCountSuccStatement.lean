import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnimodularHermitianRepsCountSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unimodular_hermitian_reps_count_succ : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R), IsUnimod σ S → IsUnimod σ T → ∀ k : ℕ, 1 ≤ k → solCount σ ϖ S T (k + 1) = solCount σ ϖ S T k * q ^ (2 * m * n - n ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.solCount_succ | exact GlobalTheory.CompanionTheory.UnrDens.solCount_succ | (intros; apply GlobalTheory.CompanionTheory.UnrDens.solCount_succ <;> assumption)
