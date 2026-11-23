import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleComponentsNoetherianFinite
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
theorem _root_.GlobalTheory.T.irreducible_components_noetherian_finite : ∀ (X : Type) [TopologicalSpace X] [NoetherianSpace X] (S : Set X), IsClosed S → {W : Set X | Maximal (fun W : Set X => _root_.IsIrreducible W ∧ W ⊆ S) W}.Finite ∧ ⋃₀ {W : Set X | Maximal (fun W : Set X => _root_.IsIrreducible W ∧ W ⊆ S) W} = S ∧ ∀ W : Set X, Maximal (fun W : Set X => _root_.IsIrreducible W ∧ W ⊆ S) W → IsClosed W := by
  first | exact @GlobalTheory.closed_eq_sUnion_maximal_irreducible | exact GlobalTheory.closed_eq_sUnion_maximal_irreducible | (intros; apply GlobalTheory.closed_eq_sUnion_maximal_irreducible <;> assumption)
