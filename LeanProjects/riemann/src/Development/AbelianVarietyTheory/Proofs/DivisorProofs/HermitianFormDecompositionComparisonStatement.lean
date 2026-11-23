import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormDecompositionComparison
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedPotentialLogGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparableHermitianFormsDetBounds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
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
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.QCoh (pullbackSections)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_decomposition_comparison : ∀ {g : ℕ} {ι Tau : Type} [Fintype Tau] {d : Tau → ℕ} (v : ι → Fin g → ℂ), Submodule.span ℂ (Set.range v) = ⊤ → ∀ (Gm Gm' : Matrix (Fin g) (Fin g) ℂ), Gm.IsHermitian → Gm'.IsHermitian → ∀ (A A' : ∀ τ, Matrix (Fin (d τ)) (Fin (d τ)) ℂ) (x : ∀ τ, ι → Fin (d τ) → ℂ), (∀ i i', HermFrame.form Gm (v i) (v i') = ∑ τ, HermFrame.form (A τ) (x τ i) (x τ i')) → (∀ i i', HermFrame.form Gm' (v i) (v i') = ∑ τ, HermFrame.form (A' τ) (x τ i) (x τ i')) → ∀ (K : ℝ), (∀ τ, (((K : ℂ) • A' τ) - A τ).PosSemidef) → (((K : ℂ) • Gm') - Gm).PosSemidef := by
  first | exact @GlobalTheory.SpanCompare.posSemidef_of_span | exact GlobalTheory.SpanCompare.posSemidef_of_span | (intros; apply GlobalTheory.SpanCompare.posSemidef_of_span <;> assumption)
