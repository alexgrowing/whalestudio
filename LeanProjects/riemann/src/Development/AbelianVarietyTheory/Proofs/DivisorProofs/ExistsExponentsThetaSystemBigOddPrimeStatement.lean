import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExponentsThetaSystemBigOddPrime
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_exponents_thetaSystem_big_odd_prime : ∀ (g n : ℕ), n.Prime → Odd n → ∃ k j : ℕ, 2 ≤ k ∧ 1 ≤ j ∧ ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω), S.g = g → S.N = (n ^ k) ^ 2 → S.r = n ^ j → S.Big := by
  first | exact @GlobalTheory.Mum.bigSizes | exact GlobalTheory.Mum.bigSizes | (intros; apply GlobalTheory.Mum.bigSizes <;> assumption)
