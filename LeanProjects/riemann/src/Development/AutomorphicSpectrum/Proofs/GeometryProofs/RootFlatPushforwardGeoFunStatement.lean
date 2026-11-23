import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootFlatPushforwardGeoFun
import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PropFTop
open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_flat_pushforward_geoFun : PtsIntegrableStatement → MetricLocalStatement → DegreeStatement → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (II : IntersectionSystem) (τ : Ψ) (R : RootFlat M τ) (Q : RP Ψ N), IsIntersectionSystem II → M.Converges II → Q.IsHomogeneous (dimFl Ψ N) → M.PP II (toA (pk τ 1 * Q)) = R.ht * M.geoFun (toA Q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.root_flat_pushforward_eq | exact GlobalTheory.CompanionTheory.Ar.Flat.root_flat_pushforward_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.root_flat_pushforward_eq <;> assumption)
