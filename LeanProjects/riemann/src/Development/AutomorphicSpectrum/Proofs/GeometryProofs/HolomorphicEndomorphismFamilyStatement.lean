import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicEndomorphismFamily
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_endomorphism_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (ρ : ℝ) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M (Metric.ball 0 ρ) ψ), 0 < ρ → ∃ B : (Fin n → ℂ) → (𝓞 E →+* Module.End ℂ (Fin g → ℂ)), (∀ c x, DifferentiableOn ℂ (fun b => B b c x) (Metric.ball 0 ρ)) ∧ ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ c x, e.ex b (B b c x) = e.ex b x ≫ t.act.act c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ActFam.exists_action_family | exact GlobalTheory.CompanionTheory.Ar.Flat.ActFam.exists_action_family | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ActFam.exists_action_family <;> assumption)
