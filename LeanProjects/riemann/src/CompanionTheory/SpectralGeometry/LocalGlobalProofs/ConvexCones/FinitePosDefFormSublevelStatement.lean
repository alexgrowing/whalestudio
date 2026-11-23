import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.FinitePosDefFormSublevel
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_pos_def_form_sublevel : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X] (β : LinearMap.BilinForm ℤ X), (∀ y z, β y z = β z y) → (∀ y, y ≠ 0 → 0 < β y y) → ∀ c : ℤ, {y : X | β y y ≤ c}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.sublevel_finite | exact GlobalTheory.CompanionTheory.Ar.Fan.sublevel_finite | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.sublevel_finite <;> assumption)
