import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem polAV_g_eq_of_isGrpPullback : ∀ (K : Type) [Field K] (T : Scheme.{0}) (P : PolAV T) (P₀ : PolAV (Sp K)) (f : Sp K ⟶ T) (a : P₀.A.left ⟶ P.A.left), IsGrpPullback P₀.A P.A f a → P₀.g = P.g := by
  intro K _ T P P₀ f a h
  have h2 : SmoothOfRelativeDimension P.g P₀.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
  exact ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ P₀.smoothDim h2 (eSec P₀.A (default : PrimeSpectrum K))

end GlobalTheory
