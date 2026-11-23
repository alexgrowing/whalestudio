import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesTaylorSubstFirstOrder
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeries_taylor_subst_first_order : ∀ (k : Type) [Field k] (φ a b : PowerSeries k) (m : ℕ), 1 ≤ m → PowerSeries.constantCoeff a = 0 →
 PowerSeries.constantCoeff (φ.subst a : PowerSeries k) = PowerSeries.constantCoeff φ ∧
 (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ (φ.subst (a + PowerSeries.X ^ m * b) : PowerSeries k) - φ.subst a - PowerSeries.X ^ m * PowerSeries.C (PowerSeries.constantCoeff b * PowerSeries.coeff 1 φ) := by
  first | exact @GlobalTheory.taylor_subst_first_order | exact GlobalTheory.taylor_subst_first_order | (intros; apply GlobalTheory.taylor_subst_first_order <;> assumption)
