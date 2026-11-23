import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCard
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quotient_card : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ k : ℕ, Nat.card (R ⧸ lev ϖ k) = q ^ (2 * k) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.card_quot_lev | exact GlobalTheory.CompanionTheory.UnrDens.card_quot_lev | (intros; apply GlobalTheory.CompanionTheory.UnrDens.card_quot_lev <;> assumption)
