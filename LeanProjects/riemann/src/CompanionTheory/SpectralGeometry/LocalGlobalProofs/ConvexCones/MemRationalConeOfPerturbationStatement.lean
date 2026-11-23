import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MemRationalConeOfPerturbation
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_rational_cone_of_perturbation : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (B B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), (∀ ε : ℝ, 0 < ε → B + ε • B₀ ∈ rcone γ) → B ∈ rcone γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.rcone_closed_seg | exact GlobalTheory.CompanionTheory.Ar.Fan.rcone_closed_seg | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.rcone_closed_seg <;> assumption)
