import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteGeneratingValues
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbBound
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_finite_generating_values : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (z₀ : Sp ℂ ⟶ X), IsCptGen ξ → genPt ξ ⤳ centre z₀ → ∃ (N : ℕ) (s : Fin N → Li), (∀ i, ∃ v : epsAt z₀ ⟶ G, M.ValAt z₀ (s i) v) ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel G z₀ V) (b : Fin N → V), (∀ i, M.ValAt z₀ (s i) (Mz.pt (b i))) → LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotUnif.lie_frame_values_basis | exact GlobalTheory.CompanionTheory.Ar.QuotUnif.lie_frame_values_basis | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotUnif.lie_frame_values_basis <;> assumption)
