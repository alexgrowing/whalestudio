import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundarySettingHeightComparison
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOnNhdOffBoundary
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
theorem _root_.GlobalTheory.T.boundary_setting_height_comparison : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (σ : κ.c.F →+* ℂ) [CompactSpace (CxPts (genStr s.T.Z) σ)] (m : ℕ) (α : LocPot (CxPts (genStr s.T.Z) σ)) (Λ : Fin m → LocPot (CxPts (genStr s.T.Z) σ)) (sg : Fin m → CxPts (genStr s.T.Z) σ → CxPts (genStr s.T.Z) σ → ℂ) (t : ℝ), IsBoundarySetting (manifold s.T.Z σ).finAtlas α Λ sg t → ∀ (Y : Scheme.{0}) (q : Y ⟶ Sp (𝓞 κ.c.F)) (jm : Y ⟶ s.T.Z.X) (hq : jm ≫ s.T.Z.s = q) (n : ℕ) (ch : AlgChart q (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F)) n), (∀ (x : CxPts (genStr s.T.Z) σ) (y : CxPts q (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F))), y ∈ ch.e.source → up jm hq σ y ∉ boundary sg → up jm hq σ y ∈ α.U x → ∃ O : Set (V n), IsOpen O ∧ ch.e y ∈ O ∧ O ⊆ ch.e.target ∧ ContDiffOn ℝ ∞ (fun v => (poincarePot α Λ sg t).φ x (up jm hq σ (ch.e.symm v))) O) → (∀ (x x' : CxPts (genStr s.T.Z) σ) (y : CxPts q (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F))), y ∈ ch.e.source → up jm hq σ y ∉ boundary sg → up jm hq σ y ∈ α.U x → up jm hq σ y ∈ α.U x' → cHess n (fun v => ((poincarePot α Λ sg t).φ x (up jm hq σ (ch.e.symm v)) : ℂ)) (ch.e y) = cHess n (fun v => ((poincarePot α Λ sg t).φ x' (up jm hq σ (ch.e.symm v)) : ℂ)) (ch.e y)) → AEMeasurable (fun v => potDens (poincarePot α Λ sg t) (boundary sg)ᶜ (up jm hq σ) ch (ch.e.symm v)) (volume.restrict ch.e.target) := by
  first | exact @GlobalTheory.ArchLim.PotMeas.aemeasurable_potDens_poincare | exact GlobalTheory.ArchLim.PotMeas.aemeasurable_potDens_poincare | (intros; apply GlobalTheory.ArchLim.PotMeas.aemeasurable_potDens_poincare <;> assumption)
