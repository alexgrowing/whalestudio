import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundarySettingHeightLower
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
theorem _root_.GlobalTheory.T.boundary_setting_height_lower : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (σ : κ.c.F →+* ℂ) [CompactSpace (CxPts (genStr s.T.Z) σ)] (m : ℕ) (α : LocPot (CxPts (genStr s.T.Z) σ)) (Λ : Fin m → LocPot (CxPts (genStr s.T.Z) σ)) (sg : Fin m → CxPts (genStr s.T.Z) σ → CxPts (genStr s.T.Z) σ → ℂ) (t : ℝ), IsBoundarySetting (manifold s.T.Z σ).finAtlas α Λ sg t → ∀ (Y : Scheme.{0}) (q : Y ⟶ Sp (𝓞 κ.c.F)) (jm : Y ⟶ s.T.Z.X) (hq : jm ≫ s.T.Z.s = q) (n : ℕ) (ch : AlgChart q (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F)) n), (∀ (W : (gen s.T.Z).Opens) (f : Γ(gen s.T.Z, W)), DifferentiableOn ℂ (ev (genStr s.T.Z) σ W f ∘ up jm hq σ ∘ ch.e.symm) (ch.e.target ∩ ch.e.symm ⁻¹' (up jm hq σ ⁻¹' ptsIn (genStr s.T.Z) σ W))) → ∀ (x : CxPts (genStr s.T.Z) σ) (y : CxPts q (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F))), y ∈ ch.e.source → up jm hq σ y ∉ boundary sg → up jm hq σ y ∈ α.U x → ∃ O : Set (V n), IsOpen O ∧ ch.e y ∈ O ∧ O ⊆ ch.e.target ∧ ContDiffOn ℝ ∞ (fun v => (poincarePot α Λ sg t).φ x (up jm hq σ (ch.e.symm v))) O := by
  first | exact @GlobalTheory.PoincPull.smoothOn_chart_up_off_boundary | exact GlobalTheory.PoincPull.smoothOn_chart_up_off_boundary | (intros; apply GlobalTheory.PoincPull.smoothOn_chart_up_off_boundary <;> assumption)
