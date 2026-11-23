import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LieFreeNearTwoPrimes
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieBasis_away_avoiding_two_primes : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ), SmoothOfRelativeDimension n G.hom → ∀ p q : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧ r ∉ q.asIdeal ∧ ∃ v : Fin n → (epsR (Localization.Away r) ⟶ (Over.pullback (spMap (algebraMap R (Localization.Away r)))).obj G), IsLieBasis v := by
  first | exact @GlobalTheory.LieTwo.lie_free_near_two_primes | exact GlobalTheory.LieTwo.lie_free_near_two_primes | (intros; apply GlobalTheory.LieTwo.lie_free_near_two_primes <;> assumption)
