import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ZeroSectionSurjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zero_section_surjective : ∀ (X0 : Scheme.{0}) (G : Over X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (m : ℕ), Function.Surjective (secZ G x m).base := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.secZ_surj | exact GlobalTheory.CompanionTheory.Ar.Coc.secZ_surj | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.secZ_surj <;> assumption)
