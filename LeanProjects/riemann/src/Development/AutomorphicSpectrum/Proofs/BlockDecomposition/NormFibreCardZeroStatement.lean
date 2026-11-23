import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFibreCardZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_fibre_card_zero : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → (Nat.card {a : E // a * τ a = 0} : ℤ) = q * (1 + ε) - ε := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.NormZero.card_norm_zero | exact GlobalTheory.CompanionTheory.UnrDens.NormZero.card_norm_zero | (intros; apply GlobalTheory.CompanionTheory.UnrDens.NormZero.card_norm_zero <;> assumption)
