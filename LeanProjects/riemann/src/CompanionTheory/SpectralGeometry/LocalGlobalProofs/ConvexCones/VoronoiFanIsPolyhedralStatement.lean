import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.VoronoiFanIsPolyhedral
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.voronoi_fan_is_polyhedral : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g q : ℕ), (∀ (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], HasRedCover bar Y) → Module.finrank ℤ O * q ≤ g → IsPolyFan bar q (vorFun O g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.vorFun_isPolyFan | exact GlobalTheory.CompanionTheory.Ar.Fan.vorFun_isPolyFan | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.vorFun_isPolyFan <;> assumption)
