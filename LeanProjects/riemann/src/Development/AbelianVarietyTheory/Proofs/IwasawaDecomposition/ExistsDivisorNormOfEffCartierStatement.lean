import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDivisorNormOfEffCartier
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_divisor_norm_of_effCartier : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d p] (σ : k →+* ℂ) (C : Closeds Y), IsProjOver p → ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (Scheme.IdealSheafData.vanishingIdeal C) → ∃ n, IsDivNorm (AnRead.all p σ d) C n := by
  first | exact @GlobalTheory.ShFam.exists_isDivNorm | exact GlobalTheory.ShFam.exists_isDivNorm | (intros; apply GlobalTheory.ShFam.exists_isDivNorm <;> assumption)
