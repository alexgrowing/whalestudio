import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicChartIrreducibleComponentLocal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapCompSpMap
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
open GlobalTheory.HorComp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_chart_irreducible_component_local : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (σ : κ.c.F →+* ℂ) (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp (𝓞 κ.c.F)) (jm : Y ⟶ s.T.Z.X) [IsClosedImmersion jm] (hq : jm ≫ s.T.Z.s = q) (n : ℕ), IsArithVar q n → ∀ (ch : AlgChart q (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F)) n) (y : CxPts q (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F))), y ∈ ch.e.source → ∀ C ∈ irreducibleComponents (cxFib (algebraMap (𝓞 κ.c.F) κ.c.F) q σ), ∀ C' ∈ irreducibleComponents (cxFib (algebraMap (𝓞 κ.c.F) κ.c.F) q σ), up jm hq σ y ∈ ptsOf s.T.Z (toGenCx jm hq σ '' C) → up jm hq σ y ∈ ptsOf s.T.Z (toGenCx jm hq σ '' C') → C = C' := by
  first | exact @GlobalTheory.HorComp.OneComp.component_unique | exact GlobalTheory.HorComp.OneComp.component_unique | (intros; apply GlobalTheory.HorComp.OneComp.component_unique <;> assumption)
