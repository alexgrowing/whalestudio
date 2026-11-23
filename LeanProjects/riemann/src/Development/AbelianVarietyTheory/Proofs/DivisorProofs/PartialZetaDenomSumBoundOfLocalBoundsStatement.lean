import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaDenomSumBoundOfLocalBounds
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateWideInd
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialZetaDenomSumBound_of_local_bounds : ∀ {F : Type} [Field F] [NumberField F], Formalism.PairingDivisionLocalBalance.CESum → ∀ (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ), 2 ≤ k → 16 ≤ finrank ℚ F * k →
    (∀ l : ℕ, l.Prime → cE z l ≤ finrank ℚ F * padicValNat l 2 + Formalism.PairingDivisionLocalBalance.mE l (finrank ℚ F * k)) → SumBound k z := by
  first | exact @GlobalTheory.Proof.partialZetaDenomSumBound_of_local_bounds.sumBound_of_local | exact GlobalTheory.Proof.partialZetaDenomSumBound_of_local_bounds.sumBound_of_local | (intros; apply GlobalTheory.Proof.partialZetaDenomSumBound_of_local_bounds.sumBound_of_local <;> assumption)
