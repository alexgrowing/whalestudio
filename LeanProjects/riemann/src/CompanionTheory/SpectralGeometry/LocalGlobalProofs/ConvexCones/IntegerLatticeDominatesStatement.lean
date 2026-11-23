import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.IntegerLatticeDominates
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integer_lattice_dominates : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X], Dominates (id : ℤ → ℤ) X := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.dominates_int | exact GlobalTheory.CompanionTheory.Ar.Fan.dominates_int | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.dominates_int <;> assumption)
