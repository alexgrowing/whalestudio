import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TwistedModuleFiniteProjectiveRank
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_module_finite_projective_rank : ∀ (O : Type) [CommRing O] [IsDomain O] (s : O ≃+* O) (L : Type) [AddCommGroup L] [Module O L] [Module.Finite O L] [Module.Projective O L], Module.Finite O (TwMod s L) ∧ Module.Projective O (TwMod s L) ∧ Module.finrank O (TwMod s L) = Module.finrank O L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TwModule.twMod_finite_projective_finrank | exact GlobalTheory.CompanionTheory.Ar.TwModule.twMod_finite_projective_finrank | (intros; apply GlobalTheory.CompanionTheory.Ar.TwModule.twMod_finite_projective_finrank <;> assumption)
