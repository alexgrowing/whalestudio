import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowerSeriesExpansionInDeltaUnique
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.power_series_expansion_in_delta_unique : ∀ (X0 : Scheme.{0}) (G : Over X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (m : ℕ) (W : (pullback G.hom x).Opens) (f : Γ(Ym G x m, prZ G x m ⁻¹ᵁ W)), ∃! c : Fin (m + 1) → Γ(pullback G.hom x, W), f = ∑ i, ((prZ G x m).app W).hom (c i) * dltOn G x m _ ^ (i : ℕ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.Thick.sections_thick | exact GlobalTheory.CompanionTheory.Ar.Coc.Thick.sections_thick | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.Thick.sections_thick <;> assumption)
