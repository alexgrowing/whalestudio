import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TsumSchwartzBruhatLevelEqSumResidueCosets
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EchEqOneIff
open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_schwartzBruhatLevel_eq_sum_residueCosets : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] (R : ℕ) (φ F : Matrix κ ι ℚ → ℂ), 0 < R → HasLevel R φ → Summable (fun x => φ x * F x) → ∑' x, φ x * F x = ∑ n : κ → ι → Fin (R * R), φ (rep R n) * ∑' m : κ → ι → ℤ, F (rep R n + (R : ℚ) • zm m) := by
  first | exact @GlobalTheory.SW.FourierJ.tsum_level_eq_sum_cosets | exact GlobalTheory.SW.FourierJ.tsum_level_eq_sum_cosets | (intros; apply GlobalTheory.SW.FourierJ.tsum_level_eq_sum_cosets <;> assumption)
