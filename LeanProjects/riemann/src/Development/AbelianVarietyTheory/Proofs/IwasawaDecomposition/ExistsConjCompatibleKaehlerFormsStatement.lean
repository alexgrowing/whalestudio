import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjCompatibleKaehlerForms
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_compatible_kaehler_forms : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d p], IsProjOver p → ∃ a : ∀ σ : k →+* ℂ, ChartForm p σ d, (∀ σ, IsKaehlerForm (AnRead.all p σ d) (a σ)) ∧ ∀ σ σ' (j : CxPts p σ' → CxPts p σ), IsConjMap j → ∀ W φ, IsPotential (AnRead.all p σ d) (a σ) W φ → IsPotential (AnRead.all p σ' d) (a σ') (j ⁻¹' W) (φ ∘ j) := by
  first | exact @GlobalTheory.KaehlerFamily.exists_kaehlerFamily | exact GlobalTheory.KaehlerFamily.exists_kaehlerFamily | (intros; apply GlobalTheory.KaehlerFamily.exists_kaehlerFamily <;> assumption)
