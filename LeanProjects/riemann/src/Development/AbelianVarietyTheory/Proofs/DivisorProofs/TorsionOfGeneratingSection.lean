import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveWeightSection
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_of_generating_section : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [Algebra ℚ R] (gb : GBase D.toG R) (N : ℕ), 3 ≤ N → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GObj gb N s), ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ o.A), (∃ t : (o.P.pull (lift (snd o.A T ≫ x) (fst o.A T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  first | (exact @GlobalTheory.UPel.HT.GenKer.exists_coprime_pow_eq_one) | (exact GlobalTheory.UPel.HT.GenKer.exists_coprime_pow_eq_one) | (intros; apply GlobalTheory.UPel.HT.GenKer.exists_coprime_pow_eq_one <;> assumption)
