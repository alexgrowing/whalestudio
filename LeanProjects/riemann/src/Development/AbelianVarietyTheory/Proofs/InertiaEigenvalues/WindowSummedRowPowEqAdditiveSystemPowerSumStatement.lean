import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WindowSummedRowPowEqAdditiveSystemPowerSum
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowTEqRowS
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.windowSummedRow_pow_eq_additiveSystemPowerSum : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F) (lam π : Fin h → F) (L U : ℕ), 1 ≤ L → ∀ (z : Fin h → F) (r : Fin h), (rowS p ϖ lam L U (winPt p π L z) r / (lam r * π r ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ)) = gsum (p ^ h) (L + U) (coefB p ϖ lam π L U) z r := by
  first | exact @GlobalTheory.PMonE.rowS_winPt_pow_eq_gsum_coefB | exact GlobalTheory.PMonE.rowS_winPt_pow_eq_gsum_coefB | (intros; apply GlobalTheory.PMonE.rowS_winPt_pow_eq_gsum_coefB <;> assumption)
