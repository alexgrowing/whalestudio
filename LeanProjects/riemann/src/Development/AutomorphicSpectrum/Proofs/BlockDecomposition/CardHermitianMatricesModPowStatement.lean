import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardHermitianMatricesModPow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_hermitian_matrices_mod_pow : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ n k : ℕ, Nat.card (hermMod σ ϖ n k) = q ^ (k * n ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.card_hermMod | exact GlobalTheory.CompanionTheory.UnrDens.card_hermMod | (intros; apply GlobalTheory.CompanionTheory.UnrDens.card_hermMod <;> assumption)
