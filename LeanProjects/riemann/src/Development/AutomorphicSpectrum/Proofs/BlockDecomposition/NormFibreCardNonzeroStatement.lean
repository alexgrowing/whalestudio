import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFibreCardNonzero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_fibre_card_nonzero : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ t : E, τ t = t → t ≠ 0 → (Nat.card {a : E // a * τ a = t} : ℤ) = q - ε := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.NormUnit.card_fibre | exact GlobalTheory.CompanionTheory.UnrDens.NormUnit.card_fibre | (intros; apply GlobalTheory.CompanionTheory.UnrDens.NormUnit.card_fibre <;> assumption)
