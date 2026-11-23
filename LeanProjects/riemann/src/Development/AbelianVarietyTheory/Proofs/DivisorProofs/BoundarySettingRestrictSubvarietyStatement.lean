import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundarySettingRestrictSubvariety
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
theorem _root_.GlobalTheory.T.boundary_setting_restrict_subvariety : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (σ : κ.c.F →+* ℂ) [CompactSpace (CxPts (genStr s.T.Z) σ)] (m : ℕ) (α : LocPot (CxPts (genStr s.T.Z) σ)) (Λ : Fin m → LocPot (CxPts (genStr s.T.Z) σ)) (sg : Fin m → CxPts (genStr s.T.Z) σ → CxPts (genStr s.T.Z) σ → ℂ) (t : ℝ), IsBoundarySetting (manifold s.T.Z σ).finAtlas α Λ sg t → ∀ (Y : Scheme.{0}) (q : Y ⟶ Sp _) (jm : Y ⟶ s.T.Z.X) (hq : jm ≫ s.T.Z.s = q) (n : ℕ), IsMDens (D := n) (potDens (poincarePot α Λ sg t) (boundary sg)ᶜ (up jm hq σ)) := by
  first | exact @GlobalTheory.ArchLim.isMDens_potDens_poincarePot | exact GlobalTheory.ArchLim.isMDens_potDens_poincarePot | (intros; apply GlobalTheory.ArchLim.isMDens_potDens_poincarePot <;> assumption)
