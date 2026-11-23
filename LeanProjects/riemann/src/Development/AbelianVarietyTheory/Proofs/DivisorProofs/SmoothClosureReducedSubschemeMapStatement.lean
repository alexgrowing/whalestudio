import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothClosureReducedSubschemeMap
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
theorem _root_.GlobalTheory.T.smooth_closure_reduced_subscheme_map : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (F : FlagSp E r) (N : HermLB p) (z : X) (y : F.Y), Smooth F.π → closure {y} = F.π ⁻¹' closure {z} → ∃ (ρ : (Scheme.IdealSheafData.vanishingIdeal (clo y)).subscheme ⟶ (Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme) (_ : ρ ≫ redι (clo z) = redι (clo y) ≫ F.π) (w : ρ ≫ redι (clo z) ≫ p = redι (clo y) ≫ F.π ≫ p) (fl : Vert.Flag ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback (redι (clo z))).obj E)) r), IsFlagBundle ρ (fun _ : Unit => (Scheme.Modules.pullback (redι (clo z))).obj E) (fun _ => r) (fun _ => fl) ∧ ((F.fam H N none).restr (redι (clo y))).Isometric ((N.restr (redι (clo z))).pull ρ w) ∧ ∀ i, ((F.fam H N (some i)).restr (redι (clo y))).Isometric (VMetric.grLB fl i ((H.pull (redι (clo z)) rfl).pull ρ w)) := by
  first | exact @GlobalTheory.CloFlag.exists_isFlagBundle_clo | exact GlobalTheory.CloFlag.exists_isFlagBundle_clo | (intros; apply GlobalTheory.CloFlag.exists_isFlagBundle_clo <;> assumption)
