import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapCompSpMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryIntegralOffStrata
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

theorem GlobalTheory.HorComp.exists_straightening_range_up : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (σ : κ.c.F →+* ℂ) [CompactSpace (CxPts (genStr s.T.Z) σ)] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp (𝓞 κ.c.F)) (jm : Y ⟶ s.T.Z.X) [IsClosedImmersion jm] (hq : jm ≫ s.T.Z.s = q) (n : ℕ), IsArithVar q n → ∀ (ch : AlgChart q (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F)) n) (y : CxPts q (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F))), y ∈ ch.e.source → ∃ ψ, GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions.IsStraightening (manifold s.T.Z σ).finAtlas (Set.range (up jm hq σ)) n ψ ∧ up jm hq σ y ∈ ψ.source := by
  intro D A N j S κ s σ _ Y _ q jm _ hq n _ ch y hy
  have hA := (manifold s.T.Z σ).isAlgAtlas_finAtlas
  obtain ⟨kk, hk⟩ := (manifold s.T.Z σ).finAtlas.cover (up jm hq σ y)
  obtain ⟨c0, hc0⟩ := hA kk
  have hk0 : up jm hq σ y ∈ c0.e.source := by rw [hc0] at hk; exact hk
  obtain ⟨-, hanF, hinjF⟩ := GlobalTheory.UpMeas.up_fin jm hq σ ch c0 hy hk0
  obtain ⟨ψ, hψ, hyψ, -⟩ := GlobalTheory.UpMeas.exists_straightening (manifold s.T.Z σ).finAtlas
    (GlobalTheory.UpMeas.isEmbedding_up jm hq σ).isInducing ch.finChart hy c0.finChart
    (hA.isCompatChart c0) hk0 hanF hinjF isOpen_univ (Set.mem_univ _) rfl
  exact ⟨ψ, hψ, hyψ⟩
