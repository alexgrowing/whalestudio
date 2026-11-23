import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIrreducibleComponentsComplexFibre
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
theorem _root_.GlobalTheory.T.finite_irreducible_components_complex_fibre : ∀ (k F : Type) [CommRing k] [CommRing F] (β : k →+* F) (Y : Scheme.{0}) (q : Y ⟶ Sp k) (σ : F →+* ℂ) (n : ℕ), IsArithVar q n → (irreducibleComponents (cxFib β q σ)).Finite := by
  first | exact @GlobalTheory.HorComp.finite_irreducibleComponents_cxFib | exact GlobalTheory.HorComp.finite_irreducibleComponents_cxFib | (intros; apply GlobalTheory.HorComp.finite_irreducibleComponents_cxFib <;> assumption)
