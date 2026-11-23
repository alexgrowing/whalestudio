import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumAbsNormRpowNegLeDedekindZetaBound
import Formalism.HermitianLattices.StatementMass
open MeasureTheory NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_absNorm_rpow_neg_le_dedekindZeta_bound : ∀ (K : Type) [Field K] [NumberField K] (s : ℝ), 1 < s → ∀ (S : Finset (Ideal (𝓞 K))), (∀ I ∈ S, I ≠ ⊥) → ∑ I ∈ S, (Ideal.absNorm I : ℝ) ^ (-s) ≤ (s / (s - 1)) ^ Module.finrank ℚ K := by
  first | exact @GlobalTheory.IdealZetaSum.sum_absNorm_rpow_neg_le | exact GlobalTheory.IdealZetaSum.sum_absNorm_rpow_neg_le | (intros; apply GlobalTheory.IdealZetaSum.sum_absNorm_rpow_neg_le <;> assumption)
