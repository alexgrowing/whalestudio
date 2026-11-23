import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HarrisTaylorOrderSplitAlmostAllPrimes
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
open NumberField
open GlobalTheory.UPel.HT.Gen
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylorOrder_split_almost_all_primes : ∀ (G : GDatum), ∃ M : ℕ, 0 < M ∧ ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M → Nonempty ((G.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 G.F] Matrix (Fin G.m) (Fin G.m) (𝓞 G.F ⊗[ℤ] ℤ_[p])) := by
  first | (exact @GlobalTheory.UPel.HT.Gen.SplitAE.splitAE) | (exact GlobalTheory.UPel.HT.Gen.SplitAE.splitAE) | (intros; apply GlobalTheory.UPel.HT.Gen.SplitAE.splitAE  <;> assumption)
