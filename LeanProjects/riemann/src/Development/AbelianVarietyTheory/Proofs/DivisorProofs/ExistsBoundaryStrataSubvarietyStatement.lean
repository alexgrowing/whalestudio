import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundaryStrataSubvariety
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
theorem _root_.GlobalTheory.T.exists_boundary_strata_subvariety : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) [CompactSpace (CxPts (genStr s.T.Z) σ)] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp _) (jm : Y ⟶ s.T.Z.X) [IsClosedImmersion jm] (hq : jm ≫ s.T.Z.s = q) (n : ℕ), IsArithVar q n → jm (genericPoint Y) ∈ abLocus s.T.Z.t.G → ∃ (m : ℕ) (Zs : Fin m → Set (CxPts (genStr s.T.Z) σ)) (T₀ : Set Y), IsClosed T₀ ∧ genericPoint Y ∉ T₀ ∧ (∀ a, IsIrreducibleAnalytic (manifold s.T.Z σ).finAtlas (Zs a) ∧ (regularLocus (manifold s.T.Z σ).finAtlas (Zs a) n).Nonempty ∧ Zs a ⊆ Set.range (up jm hq σ)) ∧ (∀ y : CxPts q (σ.comp _), y.1 (IsLocalRing.closedPoint ℂ) ∉ T₀ → ∃ a W, IsOpen W ∧ up jm hq σ y ∈ W ∧ W ∩ Set.range (up jm hq σ) = W ∩ Zs a) ∧ (∀ a (T : Set Y), IsClosed T → genericPoint Y ∉ T → ∃ y : CxPts q (σ.comp _), up jm hq σ y ∈ Zs a ∧ y.1 (IsLocalRing.closedPoint ℂ) ∉ T) ∧ ∀ a C, IsIrreducibleComponent (manifold s.T.Z σ).finAtlas (Zs a ∩ {y | ¬ Inner y}) C → ∀ T : Set Y, IsClosed T → (∀ y : CxPts q (σ.comp _), up jm hq σ y ∈ C → y.1 (IsLocalRing.closedPoint ℂ) ∈ T) → ∃ v ∈ T, jm v ∉ abLocus s.T.Z.t.G ∧ CharZero (Y.residueField v) ∧ Order.coheight v = 1 := by
  first | exact @GlobalTheory.HorComp.analytic_components | exact GlobalTheory.HorComp.analytic_components | (intros; apply GlobalTheory.HorComp.analytic_components <;> assumption)
