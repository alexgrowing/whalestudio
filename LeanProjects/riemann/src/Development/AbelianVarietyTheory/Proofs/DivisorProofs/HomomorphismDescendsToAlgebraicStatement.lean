import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismDescendsToAlgebraic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homomorphism_descends_to_algebraic : ∀ (A₀ B₀ : Over (Sp Qb)) [GrpObj A₀] [GrpObj B₀] (A B : Over (Sp ℂ)) [GrpObj A] [GrpObj B]
    (p : A.left ⟶ A₀.left) (q : B.left ⟶ B₀.left) (g g' : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom →
    IsAbelianScheme B₀ → SmoothOfRelativeDimension g' B₀.hom →
    IsGrpPullback A A₀ (spMap (algebraMap Qb ℂ)) p → IsGrpPullback B B₀ (spMap (algebraMap Qb ℂ)) q →
    ∀ α : A ⟶ B, IsMonHom α → ∃ α₀ : A₀ ⟶ B₀, IsMonHom α₀ ∧ α.left ≫ q = p ≫ α₀.left := by
  first | exact @GlobalTheory.HomDescentQb.hom_descends | exact GlobalTheory.HomDescentQb.hom_descends | (intros; apply GlobalTheory.HomDescentQb.hom_descends <;> assumption)
