import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnOfHoloOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicChartHolomorphicEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicChartAnalyticRegularFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleClosedAffinePrimeIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePrimeComplexCoordinateRingStatement
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

namespace GlobalTheory.IrrAn

theorem exists_open_preconnected_locIdent : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [LocallyOfFiniteType p] (σ : k →+* ℂ) (d : ℕ) (R : AnRead p σ d) [CompactSpace (CxPts p σ)] (T : Set (Limits.pullback p (spMap σ) : Scheme.{0})), IsClosed T → IsIrreducible T → ∃ W : (Limits.pullback p (spMap σ) : Scheme.{0}).Opens, (T ∩ (W : Set (Limits.pullback p (spMap σ) : Scheme.{0}))).Nonempty ∧ IsPreconnected (GlobalTheory.IrrAn.ptsOf p σ (T ∩ (W : Set (Limits.pullback p (spMap σ) : Scheme.{0})))) ∧ GlobalTheory.IrrAn.LocIdent R.finAtlas (GlobalTheory.IrrAn.ptsOf p σ (T ∩ (W : Set (Limits.pullback p (spMap σ) : Scheme.{0})))) := by
  intro k _ X p _ σ d R _ T hT hirr
  obtain ⟨W, hW, hne, P, hP, hcorr, hrest⟩ := GlobalTheory.T.irreducible_closed_affine_prime_ideal k X p σ T hT hirr
  letI : Algebra ℂ Γ((Limits.pullback p (spMap σ) : Scheme.{0}), W) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (Limits.pullback.snd p (spMap σ)) W).toAlgebra
  obtain ⟨hft, d', hch⟩ := hrest
  haveI := hP
  obtain ⟨ι, hemb, hrange, han⟩ := GlobalTheory.T.affine_prime_complex_coordinate_ring k X p σ T W hW P hcorr
  refine ⟨W, hne, ?_⟩
  have hpull := GlobalTheory.T.algebraic_chart_analytic_regular_functions k X p σ d R _ d' ι hemb.continuous (han d')
  obtain ⟨h1, h2⟩ := GlobalTheory.T.algebraic_chart_holomorphic_embedding d (CxPts p σ) R.finAtlas _ d' ι hch hemb
    (fun O g hO hg e he => hpull O g hO ((R.finAtlas_holoOn_iff hO).1 hg) e he)
  rw [← hrange]
  exact ⟨h1, h2⟩

end GlobalTheory.IrrAn
