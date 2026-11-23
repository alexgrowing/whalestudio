import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleClosedAffinePrimeIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnOfHoloOn
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
open GlobalTheory.IrrAn
open scoped GlobalTheory.AffinePoints
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_closed_affine_prime_ideal : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [LocallyOfFiniteType p] (σ : k →+* ℂ) (T : Set (Limits.pullback p (spMap σ) : Scheme.{0})), IsClosed T → IsIrreducible T → ∃ (W : (Limits.pullback p (spMap σ) : Scheme.{0}).Opens) (hW : IsAffineOpen W), (T ∩ (W : Set (Limits.pullback p (spMap σ) : Scheme.{0}))).Nonempty ∧ ∃ P : Ideal Γ((Limits.pullback p (spMap σ) : Scheme.{0}), W), P.IsPrime ∧ (∀ x : W, (x : (Limits.pullback p (spMap σ) : Scheme.{0})) ∈ T ↔ P ≤ (hW.primeIdealOf x).asIdeal) ∧ letI : Algebra ℂ Γ((Limits.pullback p (spMap σ) : Scheme.{0}), W) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (Limits.pullback.snd p (spMap σ)) W).toAlgebra; Algebra.FiniteType ℂ (Γ((Limits.pullback p (spMap σ) : Scheme.{0}), W) ⧸ P) ∧ ∃ d' : ℕ, GlobalTheory.AffinePoints.HasAlgebraicCharts ℂ (Γ((Limits.pullback p (spMap σ) : Scheme.{0}), W) ⧸ P) d' := by
  first | exact @GlobalTheory.IrrSmooth.exists_affine_smooth_prime | exact GlobalTheory.IrrSmooth.exists_affine_smooth_prime | (intros; apply GlobalTheory.IrrSmooth.exists_affine_smooth_prime <;> assumption)
