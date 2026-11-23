import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyLaEqPow
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_la_eq_pow : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (c : 𝓞 D.F), haveI := D.freeLa; haveI := D.finLa; LinearMap.charpoly (DistribMulAction.toLinearMap ℤ D.La (algebraMap (𝓞 D.F) D.O c)) = (LinearMap.charpoly (LinearMap.mulLeft ℤ c)) ^ (D.m * D.n) := by
  first | (exact @GlobalTheory.UPel.HT.Datum.charpoly_La_eq_pow) | (exact GlobalTheory.UPel.HT.Datum.charpoly_La_eq_pow) | (intros; apply GlobalTheory.UPel.HT.Datum.charpoly_La_eq_pow  <;> assumption)
