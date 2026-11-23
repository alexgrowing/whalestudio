import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjIdempotentModPrimePow
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_idempotent_mod_prime_pow : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (r : ℕ), ∃ ε u v : 𝓞 D.F, ε + D.bar ε = 1 + (p : 𝓞 D.F) ^ r * u ∧ ε * D.bar ε = (p : 𝓞 D.F) ^ r * v := by
  first | (exact @GlobalTheory.UPel.HT.SplitIdem.exists_conj_idem) | (exact GlobalTheory.UPel.HT.SplitIdem.exists_conj_idem) | (intros; apply GlobalTheory.UPel.HT.SplitIdem.exists_conj_idem  <;> assumption)
