import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFiniteFlat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_finite_flat : ∀ (A X : Over (Sp ℂ)) [GrpObj A] [GrpObj X] (g : ℕ), IsAbelianScheme A → IsAbelianScheme X →
    SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g X.hom →
    ∀ (ψ : A ⟶ X) [IsMonHom ψ] [Surjective ψ.left], IsFinite ψ.left ∧ Flat ψ.left := by
  first | exact @GlobalTheory.SurjHomFlat.finite_flat | exact GlobalTheory.SurjHomFlat.finite_flat | (intros; apply GlobalTheory.SurjHomFlat.finite_flat <;> assumption)
