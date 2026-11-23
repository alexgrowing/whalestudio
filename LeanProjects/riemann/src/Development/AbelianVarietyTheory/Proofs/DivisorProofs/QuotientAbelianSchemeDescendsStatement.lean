import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientAbelianSchemeDescends
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_abelian_scheme_descends : ∀ (A₀ : Over (Sp Qb)) [GrpObj A₀] (A X : Over (Sp ℂ)) [GrpObj A] [GrpObj X] (p : A.left ⟶ A₀.left) (g : ℕ),
    IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → IsGrpPullback A A₀ (spMap (algebraMap Qb ℂ)) p →
    IsAbelianScheme X → SmoothOfRelativeDimension g X.hom → ∀ ψ : A ⟶ X, IsMonHom ψ →
    (∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ X, ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ ψ = y) →
  ∃ (X₀ : Over (Sp Qb)) (_ : GrpObj X₀) (q : X.left ⟶ X₀.left), IsAbelianScheme X₀ ∧ SmoothOfRelativeDimension g X₀.hom ∧
    IsGrpPullback X X₀ (spMap (algebraMap Qb ℂ)) q := by
  first | exact @GlobalTheory.IsogModel.exists_model_of_surjective | exact GlobalTheory.IsogModel.exists_model_of_surjective | (intros; apply GlobalTheory.IsogModel.exists_model_of_surjective <;> assumption)
