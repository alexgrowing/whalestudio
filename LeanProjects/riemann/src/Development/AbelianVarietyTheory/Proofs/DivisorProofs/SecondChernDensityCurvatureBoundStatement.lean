import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensityCurvatureBound
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
theorem _root_.GlobalTheory.T.second_chern_density_curvature_bound : ∀ (e : ℕ) (T : Type) [Fintype T] (μ : T → ℕ) (C : ℝ), ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (U : Set (V (e + 2))) (H : ∀ τ, V (e + 2) → Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ), (∀ τ, IsPosFrame U (H τ)) → ∀ u ∈ U, ∀ G : Matrix (Fin (e + 2)) (Fin (e + 2)) ℂ, G.PosSemidef → (∀ τ (ξ η : V (e + 2)), opNorm (H τ u) (H τ u) (curv (H τ) u ξ η) ≤ C * gnorm G ξ.ofLp * gnorm G η.ofLp) → |secondChernDensity e (fun ξ₁ η₁ ξ₂ η₂ => ∑ τ, chTwo (H τ) u ξ₁ η₁ ξ₂ η₂) (Matrix.of fun a b => -∑ τ, (curv (H τ) u (bas _ a) (bas _ b)).trace)| ≤ C' * G.det.re := by
  first | exact @GlobalTheory.ChDens.dens22_le | exact GlobalTheory.ChDens.dens22_le | (intros; apply GlobalTheory.ChDens.dens22_le <;> assumption)
