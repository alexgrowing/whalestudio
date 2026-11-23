import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatIntegralEqSumResidueRepresentative
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EchEqOneIff
open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhatIntegral_eq_sum_residueRepresentatives : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] (R : ℕ) (φ : Matrix κ ι ℚ → ℂ), 0 < R → HasLevel R φ → haar φ = ((R : ℂ) ^ (Fintype.card κ * Fintype.card ι))⁻¹ * ∑ n : κ → ι → Fin (R * R), φ (rep R n) := by
  first | exact @GlobalTheory.SW.FourierJ.haar_eq_sum_rep | exact GlobalTheory.SW.FourierJ.haar_eq_sum_rep | (intros; apply GlobalTheory.SW.FourierJ.haar_eq_sum_rep <;> assumption)
