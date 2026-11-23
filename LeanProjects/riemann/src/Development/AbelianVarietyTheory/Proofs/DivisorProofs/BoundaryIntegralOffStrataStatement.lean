import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryIntegralOffStrata
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
theorem _root_.GlobalTheory.T.boundary_integral_off_strata : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (σ : κ.c.F →+* ℂ) [CompactSpace (CxPts (genStr s.T.Z) σ)] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp _) (jm : Y ⟶ s.T.Z.X) [IsClosedImmersion jm] (hq : jm ≫ s.T.Z.s = q) (n : ℕ), IsArithVar q n → ∀ (m : ℕ) (Zs : Fin m → Set (CxPts (genStr s.T.Z) σ)) (T₀ : Set Y), IsClosed T₀ → genericPoint Y ∉ T₀ → (∀ y : CxPts q (σ.comp _), y.1 (IsLocalRing.closedPoint ℂ) ∉ T₀ → ∃ a W, IsOpen W ∧ up jm hq σ y ∈ W ∧ W ∩ Set.range (up jm hq σ) = W ∩ Zs a) → ∀ (P : LocPot (CxPts (genStr s.T.Z) σ)) (Bd : Set (CxPts (genStr s.T.Z) σ)), IsClosed Bd → (∀ y, y ∉ Bd → ∃ W, IsOpen W ∧ y ∈ W ∧ W ⊆ P.U y ∧ ((manifold s.T.Z σ).finAtlas).SmoothOn W (P.φ y)) → IsMDens (D := n) (potDens P Bdᶜ (up jm hq σ)) → ∀ f : CxPts (genStr s.T.Z) σ → ℝ≥0∞, ∫⁻ y, f (up jm hq σ y) ∂part (D := n) (potDens P Bdᶜ (up jm hq σ)) ≤ ∑ a, regIntegral (manifold s.T.Z σ).finAtlas (Zs a) n P (regularLocus (manifold s.T.Z σ).finAtlas (Zs a) n \ Bd) f := by
  first | exact @GlobalTheory.UpMeas.lintegral_up_le_regIntegral | exact GlobalTheory.UpMeas.lintegral_up_le_regIntegral | (intros; apply GlobalTheory.UpMeas.lintegral_up_le_regIntegral <;> assumption)
