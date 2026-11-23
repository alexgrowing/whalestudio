import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjCompatibleLieMetric
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_compatible_lie_metric : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d p] (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (f : Y ⟶ X), IsProjOver p → (∀ σ : k →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ) → ∃ h : ∀ (σ : k →+* ℂ) (y : CxPts p σ), TanM (y.1 ≫ f) t.G →ₗ[ℂ] TanM (y.1 ≫ f) t.G →ₗ⋆[ℂ] ℂ, (∀ σ, IsLieMetric t f (AnRead.all p σ d) (h σ)) ∧ ∀ σ σ' (y : CxPts p σ) (y' : CxPts p σ') (v w : TanM (y.1 ≫ f) t.G) (v' w' : TanM (y'.1 ≫ f) t.G), y'.1 = spMap (starRingEnd ℂ) ≫ y.1 → (tv v').left = spMap (dualMap (starRingEnd ℂ)) ≫ (tv v).left → (tv w').left = spMap (dualMap (starRingEnd ℂ)) ≫ (tv w).left → h σ' y' v' w' = starRingEnd ℂ (h σ y v w) := by
  first | exact @GlobalTheory.LieMetConj.exists_conj_family | exact GlobalTheory.LieMetConj.exists_conj_family | (intros; apply GlobalTheory.LieMetConj.exists_conj_family <;> assumption)
