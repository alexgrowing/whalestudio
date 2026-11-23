import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramChangeBlockDiagonalFrame
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
theorem _root_.GlobalTheory.T.gram_change_block_diagonal_frame : ∀ (D : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (n : Type) [Fintype n] [DecidableEq n] (U : Set (V D)) (K : ∀ τ : ι, V D → Matrix (Fin (m τ)) (Fin (m τ)) ℂ) (T : V D → Matrix (Σ τ : ι, Fin (m τ)) n ℂ) (G : V D → Matrix n n ℂ), IsOpen U → (∀ τ, IsPosFrame U (K τ)) → (∀ j b, DifferentiableOn ℂ (fun u => T u j b) U) → (∀ u ∈ U, Function.Bijective (T u).mulVec) → (∀ u ∈ U, G u = chg (T u) (Matrix.blockDiagonal' fun τ => dualGram (K τ u))) → ∀ z ∈ U, chTwo G z = (fun ξ₁ η₁ ξ₂ η₂ => ∑ τ, chTwo (K τ) z ξ₁ η₁ ξ₂ η₂) ∧ ∀ ξ η, (curv G z ξ η).trace = -∑ τ, (curv (K τ) z ξ η).trace := by
  first | exact @GlobalTheory.HermFrame.chTwo_chg_blockDiagonal'_dualGram | exact GlobalTheory.HermFrame.chTwo_chg_blockDiagonal'_dualGram | (intros; apply GlobalTheory.HermFrame.chTwo_chg_blockDiagonal'_dualGram <;> assumption)
