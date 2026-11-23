import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicChartHolomorphicEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnOfHoloOn
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical
open GlobalTheory.IrrAn
open scoped GlobalTheory.AffinePoints
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_chart_holomorphic_embedding : ∀ (d : ℕ) (Y : Type) [TopologicalSpace Y] (A : FinHolAtlas d Y) (C : Type) [CommRing C] [IsDomain C] [Algebra ℂ C] [Algebra.FiniteType ℂ C] (d' : ℕ) (ι : (C →ₐ[ℂ] ℂ) → Y), GlobalTheory.AffinePoints.HasAlgebraicCharts ℂ C d' → Topology.IsEmbedding ι → (∀ (O : Set Y) (g : Y → ℂ), IsOpen O → A.HoloOn O g → ∀ e : OpenPartialHomeomorph (C →ₐ[ℂ] ℂ) (Fin d' → ℂ), GlobalTheory.AffinePoints.IsAlgebraicChart e → AnalyticOnNhd ℂ (g ∘ ι ∘ e.symm) (e.target ∩ e.symm ⁻¹' (ι ⁻¹' O))) → IsPreconnected (Set.range ι) ∧ GlobalTheory.IrrAn.LocIdent A (Set.range ι) := by
  first | exact @GlobalTheory.IrrAn.preconnected_locIdent_range_of_algebraicCharts | exact GlobalTheory.IrrAn.preconnected_locIdent_range_of_algebraicCharts | (intros; apply GlobalTheory.IrrAn.preconnected_locIdent_range_of_algebraicCharts <;> assumption)
