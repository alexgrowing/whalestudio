import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeformationComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_scheme_deformation_complex : ∀ (A₀ : Over (Sp ℂ)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ), (∀ a : ℂ, π (algebraMap ℂ D a) = a) → ∃ (A' : Over (Sp D)) (_ : GrpObj A') (q : A'.left ⟶ A₀.left) (i : A₀.left ⟶ A'.left), IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom ∧ IsGrpPullback A' A₀ (spMap (algebraMap ℂ D)) q ∧ IsGrpPullback A₀ A' (spMap π) i ∧ i ≫ q = 𝟙 _ := by
  first | exact @GlobalTheory.ConstLift.exists_constLift | exact GlobalTheory.ConstLift.exists_constLift | (intros; apply GlobalTheory.ConstLift.exists_constLift <;> assumption)
