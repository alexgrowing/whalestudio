import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapCompSpMap
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
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

namespace GlobalTheory.HorComp

theorem noetherianSpace_pullback_of_isProjOver {R F K : Type} [CommRing R] [CommRing F] [Field K] {X : Scheme.{0}}
    {f : X ⟶ Sp R} (h : IsProjOver f) (β : R →+* F) (σ : F →+* K) :
    NoetherianSpace (Limits.pullback (Limits.pullback.snd f (spMap β)) (spMap σ) : Scheme.{0}) := by
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver h
  let g := Limits.pullback.snd (Limits.pullback.snd f (spMap β)) (spMap σ)
  have : IsProper g := inferInstance
  have h1 := LocallyOfFiniteType.isLocallyNoetherian g
  have h2 : CompactSpace (Limits.pullback (Limits.pullback.snd f (spMap β)) (spMap σ) : Scheme.{0}) :=
    QuasiCompact.compactSpace_of_compactSpace g
  have : IsNoetherian (Limits.pullback (Limits.pullback.snd f (spMap β)) (spMap σ) : Scheme.{0}) := ⟨⟩
  infer_instance

theorem noetherianSpace_genCx : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (σ : κ.c.F →+* ℂ), NoetherianSpace (genCx s.T.Z σ) :=
  fun _ _ _ _ _ _ s σ => noetherianSpace_pullback_of_isProjOver s.T.Z.proj _ σ

end GlobalTheory.HorComp
