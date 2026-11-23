import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlphaKernelDerivativeVanishes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alpha_kernel_derivative_vanishes : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : Germ.FB R d O) (u : Fin d → R) (g : Germ.PS R 2 d), alpha B p u = 0 → pow1 B p = Germ.ev (n := 2) ![ptPow R d p 0, Germ.pt R d 1] g → ∀ j, MvPowerSeries.pderiv R ((0 : Fin 1), j) (∑ i, MvPowerSeries.C (u i) * Germ.ev (n := 1) ![0, Germ.pt R d 0] (MvPowerSeries.pderiv R ((0 : Fin 2), i) g)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Kill.germKill | exact GlobalTheory.CompanionTheory.Ar.Kill.germKill | (intros; apply GlobalTheory.CompanionTheory.Ar.Kill.germKill <;> assumption)
