import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPotentialSectionBounded
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
theorem _root_.GlobalTheory.T.exists_potential_section_bounded : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (M : DRBase O c) (m : ℕ) (sc : (lbPow M.lamB m).Sec) (σ : O.κ.c.F →+* ℂ) [CompactSpace (CxPts (genStr O.s.T.Z) σ)], ∃ (L : LocPot (CxPts (genStr O.s.T.Z) σ)) (sg : CxPts (genStr O.s.T.Z) σ → CxPts (genStr O.s.T.Z) σ → ℂ) (a : ℝ), 0 < a ∧ IsPotential (manifold O.s.T.Z σ).finAtlas L ∧ IsSection (manifold O.s.T.Z σ).finAtlas L sg ∧ (∀ y, normSec L sg y ≤ 1) ∧ ∀ y : CxPts M.q (σ.comp _), normSec L sg (up M.b rfl σ y) ^ 2 = a * (((M.lam 2).pow m).φ _).nsq (secVal M.q _ sc) y := by
  first | exact @GlobalTheory.ArchLim.exists_section_norm_le_one | exact GlobalTheory.ArchLim.exists_section_norm_le_one | (intros; apply GlobalTheory.ArchLim.exists_section_norm_le_one <;> assumption)
