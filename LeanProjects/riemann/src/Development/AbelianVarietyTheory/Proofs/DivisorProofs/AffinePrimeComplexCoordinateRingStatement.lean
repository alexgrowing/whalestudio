import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePrimeComplexCoordinateRing
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
theorem _root_.GlobalTheory.T.affine_prime_complex_coordinate_ring : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (T : Set (Limits.pullback p (spMap σ) : Scheme.{0})) (W : (Limits.pullback p (spMap σ) : Scheme.{0}).Opens) (hW : IsAffineOpen W) (P : Ideal Γ((Limits.pullback p (spMap σ) : Scheme.{0}), W)), (∀ x : W, (x : (Limits.pullback p (spMap σ) : Scheme.{0})) ∈ T ↔ P ≤ (hW.primeIdealOf x).asIdeal) → letI : Algebra ℂ Γ((Limits.pullback p (spMap σ) : Scheme.{0}), W) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (Limits.pullback.snd p (spMap σ)) W).toAlgebra; ∃ ι : ((Γ((Limits.pullback p (spMap σ) : Scheme.{0}), W) ⧸ P) →ₐ[ℂ] ℂ) → CxPts p σ, Topology.IsEmbedding ι ∧ Set.range ι = GlobalTheory.IrrAn.ptsOf p σ (T ∩ (W : Set (Limits.pullback p (spMap σ) : Scheme.{0}))) ∧ ∀ (d' : ℕ) (U : X.Opens) (f : Γ(X, U)) (e : OpenPartialHomeomorph ((Γ((Limits.pullback p (spMap σ) : Scheme.{0}), W) ⧸ P) →ₐ[ℂ] ℂ) (Fin d' → ℂ)), GlobalTheory.AffinePoints.IsAlgebraicChart e → AnalyticOnNhd ℂ (GlobalTheory.CxPts.ev p σ U f ∘ ι ∘ e.symm) (e.target ∩ e.symm ⁻¹' (ι ⁻¹' GlobalTheory.CxPts.ptsIn p σ U)) := by
  first | exact @GlobalTheory.IrrAn.exists_param | exact GlobalTheory.IrrAn.exists_param | (intros; apply GlobalTheory.IrrAn.exists_param <;> assumption)
