import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicFrameCurvatureLimit
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
theorem _root_.GlobalTheory.T.holomorphic_frame_curvature_limit : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (M : DRBase O c) (Y : Scheme.{0}) (i : Y ⟶ M.B) (hi : (i ≫ M.b) ≫ O.s.T.Z.s = i ≫ M.q) (σ : O.κ.c.F →+* ℂ) (e : ℕ) (ch : AlgChart (i ≫ M.q) (σ.comp _) (e + 2)) (cE : Chart ((Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback M.b).obj (GlobalTheory.LieVB.omega O.s.T.Z.t.G))) (D.R.f * O.N)) (U : Set (V (e + 2))) (a : V (e + 2) → CxFr O.s.T.Z σ), IsOpen U → U ⊆ ch.e.target → HolFam U a → ContinuousOn (fun u => (a u).1) U → (∀ u ∈ U, (a u).1 = up (i ≫ M.b) hi σ (ch.e.symm u)) → ∃ T : V (e + 2) → Matrix (Σ τ : D.host.E →+* ℂ, Fin (O.S.Dw.mult τ)) (Fin (D.R.f * O.N)) ℂ, (∀ j b, DifferentiableOn ℂ (fun u => T u j b) (U ∩ ch.e.symm ⁻¹' ptsIn _ _ cE.U)) ∧ (∀ u ∈ U ∩ ch.e.symm ⁻¹' ptsIn _ _ cE.U, Function.Bijective (T u).mulVec) ∧ ∀ R : ℝ, ∀ u ∈ U ∩ ch.e.symm ⁻¹' ptsIn _ _ cE.U, ((((M.h R).pull M.b rfl).pull i rfl).met (σ.comp _)).G cE (ch.e.symm u) = chg (T u) (Matrix.blockDiagonal' fun τ => dualGram (eigGram (M.x.eigMetAt σ (some R)) a τ u)) := by
  first | exact @GlobalTheory.EigGramChart.gram_eq_chg | exact GlobalTheory.EigGramChart.gram_eq_chg | (intros; apply GlobalTheory.EigGramChart.gram_eq_chg <;> assumption)
