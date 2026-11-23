import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicChartAnalyticRegularFunctions
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
theorem _root_.GlobalTheory.T.algebraic_chart_analytic_regular_functions : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (R : AnRead p σ D) (C : Type) [CommRing C] [Algebra ℂ C] (d' : ℕ) (ι : (C →ₐ[ℂ] ℂ) → CxPts p σ), Continuous ι → (∀ (U : X.Opens) (f : Γ(X, U)) (e : OpenPartialHomeomorph (C →ₐ[ℂ] ℂ) (Fin d' → ℂ)), GlobalTheory.AffinePoints.IsAlgebraicChart e → AnalyticOnNhd ℂ (GlobalTheory.CxPts.ev p σ U f ∘ ι ∘ e.symm) (e.target ∩ e.symm ⁻¹' (ι ⁻¹' GlobalTheory.CxPts.ptsIn p σ U))) → ∀ (O : Set (CxPts p σ)) (g : CxPts p σ → ℂ), IsOpen O → R.HoloOn O g → ∀ e : OpenPartialHomeomorph (C →ₐ[ℂ] ℂ) (Fin d' → ℂ), GlobalTheory.AffinePoints.IsAlgebraicChart e → AnalyticOnNhd ℂ (g ∘ ι ∘ e.symm) (e.target ∩ e.symm ⁻¹' (ι ⁻¹' O)) := by
  first | exact @GlobalTheory.analyticOnNhd_comp_algChart | exact GlobalTheory.analyticOnNhd_comp_algChart | (intros; apply GlobalTheory.analyticOnNhd_comp_algChart <;> assumption)
