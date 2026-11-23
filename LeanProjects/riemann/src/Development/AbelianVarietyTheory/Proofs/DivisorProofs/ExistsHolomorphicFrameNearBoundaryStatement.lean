import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicFrameNearBoundary
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
theorem _root_.GlobalTheory.T.exists_holomorphic_frame_near_boundary : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (M : DRBase O c) (Y : Scheme.{0}) (i : Y ⟶ M.B) (hi : (i ≫ M.b) ≫ O.s.T.Z.s = i ≫ M.q) (σ : O.κ.c.F →+* ℂ) (e : ℕ) (ch : AlgChart (i ≫ M.q) (σ.comp _) (e + 2)), ∀ y ∈ ch.e.source, ∃ (U : Set (V (e + 2))) (a : V (e + 2) → CxFr O.s.T.Z σ), IsOpen U ∧ ch.e y ∈ U ∧ HolFam U a ∧ ContinuousOn (fun u => (a u).1) U ∧ (∀ u ∈ U, (a u).1 = up (i ≫ M.b) hi σ (ch.e.symm u)) ∧ ∀ R : ℝ, (∀ τ, IsPosFrame U (eigGram (M.x.eigMetAt σ (some R)) a τ)) ∧ secondChernDensityOfMetric ((((M.h R).pull M.b rfl).pull i rfl).met _) (((M.lam R).pull i rfl).φ _) e ch y = secondChernDensity e (fun ξ₁ η₁ ξ₂ η₂ => ∑ τ, chTwo (eigGram (M.x.eigMetAt σ (some R)) a τ) (ch.e y) ξ₁ η₁ ξ₂ η₂) (Matrix.of fun a' b' => -∑ τ, (curv (eigGram (M.x.eigMetAt σ (some R)) a τ) (ch.e y) (bas _ a') (bas _ b')).trace) := by
  first | exact @GlobalTheory.ArchLim.ch2Dens_eq_eig | exact GlobalTheory.ArchLim.ch2Dens_eq_eig | (intros; apply GlobalTheory.ArchLim.ch2Dens_eq_eig <;> assumption)
