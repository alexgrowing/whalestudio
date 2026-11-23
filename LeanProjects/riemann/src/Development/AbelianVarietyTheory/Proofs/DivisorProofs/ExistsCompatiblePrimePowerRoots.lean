import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusPointOverFractionField
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_prime_power_roots : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharZero k], ∃ ζ : ℕ → kˣ, (∀ r, IsPrimitiveRoot (ζ r) (p ^ r)) ∧ ∀ r, ζ (r + 1) ^ p = ζ r := by
  first | (exact @GlobalTheory.exists_compatible_primitive_prime_pow_roots) | (exact GlobalTheory.exists_compatible_primitive_prime_pow_roots) | (intros; apply GlobalTheory.exists_compatible_primitive_prime_pow_roots  <;> assumption)
