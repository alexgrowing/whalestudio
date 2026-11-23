import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMatricesCard
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_matrices_card : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ n : ℕ, Nat.card {H : Matrix (Fin n) (Fin n) E // cT τ H = H} = q ^ (n ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.card_hermitian_resAlg | exact GlobalTheory.CompanionTheory.UnrDens.card_hermitian_resAlg | (intros; apply GlobalTheory.CompanionTheory.UnrDens.card_hermitian_resAlg <;> assumption)
