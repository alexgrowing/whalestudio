import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnOfHoloOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsEqOfLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFreeNeighbourhoodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingPairCompatibleEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxDoubledTransferStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabiliserFiniteGenerationVectorStatement
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

theorem GlobalTheory.IrrAn.irreducibleAnalytic_ptsOf : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [LocallyOfFiniteType p] (σ : k →+* ℂ) (d : ℕ) (R : AnRead p σ d) [CompactSpace (CxPts p σ)] (T : Set (Limits.pullback p (spMap σ) : Scheme.{0})), IsClosed T → IsIrreducible T → IsIrreducibleAnalytic R.finAtlas {y | (Limits.pullback.lift y.1 (𝟙 _) (y.2.trans (Category.id_comp _).symm) : Sp ℂ ⟶ Limits.pullback p (spMap σ)) (IsLocalRing.closedPoint ℂ) ∈ T} := by
  intro k _ X p _ σ d R _ T hT hirr
  change IsIrreducibleAnalytic R.finAtlas (GlobalTheory.IrrAn.ptsOf p σ T)
  refine ⟨GlobalTheory.T.closed_subset_analytic k X p σ d R T hT, GlobalTheory.T.locally_closed_analytic_nonempty k X p σ T hT.isLocallyClosed hirr.nonempty, ?_⟩
  intro Z₁ Z₂ h₁ h₂ hZ
  obtain ⟨W, hTW, hpc, hid⟩ := GlobalTheory.T.exists_open_preconnected_analytic k X p σ d R T hT hirr
  have hS : GlobalTheory.IrrAn.ptsOf p σ (T ∩ (W : Set _)) ⊆ Z₁ ∪ Z₂ :=
    hZ ▸ GlobalTheory.IrrAn.ptsOf_mono Set.inter_subset_left
  have hSne := GlobalTheory.T.locally_closed_analytic_nonempty k X p σ _ (hT.isLocallyClosed.inter W.2.isLocallyClosed) hTW
  have hd := GlobalTheory.T.irreducible_dense_open_analytic k X p σ T W hT hirr hTW
  have key : ∀ Z : Set (CxPts p σ), R.finAtlas.IsAnalyticSubset Z → Z ⊆ GlobalTheory.IrrAn.ptsOf p σ T →
      GlobalTheory.IrrAn.ptsOf p σ (T ∩ (W : Set _)) ⊆ Z → GlobalTheory.IrrAn.ptsOf p σ T = Z := fun Z hZa hZT hSZ =>
    subset_antisymm (hd.trans ((closure_mono hSZ).trans
      (GlobalTheory.IrrAn.isClosed_of_isAnalyticSubset _ hZa).closure_subset)) hZT
  rcases GlobalTheory.T.preconnected_in_union_analytic d _ R.finAtlas _ Z₁ Z₂ hpc hSne hid h₁ h₂ hS with h | h
  · exact Or.inl (key Z₁ h₁ (hZ ▸ Set.subset_union_left) h)
  · exact Or.inr (key Z₂ h₂ (hZ ▸ Set.subset_union_right) h)
