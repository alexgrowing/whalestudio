import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMatrixPullbackCell
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
theorem _root_.GlobalTheory.T.chern_matrix_pullback_cell : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (n r D : ℕ) (ε : Fin D ≃ Fin n ⊕ Low r) (σ : k →+* ℂ) (c : AlgChart q σ n) (c' : AlgChart p σ D), IsCell ε π w c c' → ∀ (N : HermLB q), ∀ y' ∈ c'.e.source, chernMat ((N.pull π w).φ σ) c' y' = cHess D (fun v => ((N.φ σ).φ (pick (N.φ σ).isLB (PtsOver.map π w (spMap σ) y')) (c.e.symm (base ε v)) : ℂ)) (c'.e y') := by
  first | exact @GlobalTheory.ArchLim.chernMat_pull_cell | exact GlobalTheory.ArchLim.chernMat_pull_cell | (intros; apply GlobalTheory.ArchLim.chernMat_pull_cell <;> assumption)
