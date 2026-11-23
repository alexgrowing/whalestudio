import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormSectionDifferenceBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_norm_section_difference_bound : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (M : DRBase O c) (m : ℕ) (sc : (lbPow M.lamB m).Sec), ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ : O.κ.c.F →+* ℂ) (R : ℝ) (y : CxPts M.q (σ.comp _)), Inner (up M.b rfl σ y) → |Real.log ((((M.lam R).pow m).φ _).nsq (secVal M.q _ sc) y) / 2 - Real.log ((((M.lam 2).pow m).φ _).nsq (secVal M.q _ sc) y) / 2| ≤ C * Real.log (M.x.r σ (up M.b rfl σ y)) := by
  first | exact @GlobalTheory.LogNormCmp.abs_log_nsq_le | exact GlobalTheory.LogNormCmp.abs_log_nsq_le | (intros; apply GlobalTheory.LogNormCmp.abs_log_nsq_le <;> assumption)
