import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointAlgebraicModel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_point_algebraic_model : ∀ (A₀ : Over (Sp Qb)) [GrpObj A₀] (A : Over (Sp ℂ)) [GrpObj A] (p : A.left ⟶ A₀.left) (g n : ℕ),
    IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → IsGrpPullback A A₀ (spMap (algebraMap Qb ℂ)) p →
    1 ≤ n → ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ^ n = 1 →
    ∃ c : 𝟙_ (Over (Sp Qb)) ⟶ A₀, x.left ≫ p = spMap (algebraMap Qb ℂ) ≫ c.left := by
  first | exact @GlobalTheory.RealMult.torsion_of_complex_is_algebraic | exact GlobalTheory.RealMult.torsion_of_complex_is_algebraic | (intros; apply GlobalTheory.RealMult.torsion_of_complex_is_algebraic <;> assumption)
