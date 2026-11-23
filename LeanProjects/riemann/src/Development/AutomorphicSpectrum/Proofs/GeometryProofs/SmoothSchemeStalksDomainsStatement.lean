import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothSchemeStalksDomains
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_scheme_stalks_domains : ∀ (K : Type) [Field K] (e : ℕ) (X : Scheme.{0}) (g : X ⟶ Sp K), SmoothOfRelativeDimension e g → ∀ x : X, IsDomain (X.presheaf.stalk x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.isDomain_stalk_of_smoothOfRelativeDimension_field | exact GlobalTheory.CompanionTheory.Ar.SncBase.isDomain_stalk_of_smoothOfRelativeDimension_field | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.isDomain_stalk_of_smoothOfRelativeDimension_field <;> assumption)
