import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIrreducibleAbelianLocusComponent
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapCompSpMap
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximal_irreducible_abelian_locus_component : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp (𝓞 κ.c.F)) (jm : Y ⟶ s.T.Z.X) [IsClosedImmersion jm] (hq : jm ≫ s.T.Z.s = q) (n : ℕ), IsArithVar q n → jm (genericPoint Y) ∈ abLocus s.T.Z.t.G → ∀ C ∈ irreducibleComponents (cxFib (algebraMap (𝓞 κ.c.F) κ.c.F) q σ), ∀ W : Set (genCx s.T.Z σ), Maximal (fun W : Set (genCx s.T.Z σ) => _root_.IsIrreducible W ∧ W ⊆ toGenCx jm hq σ '' C ∩ bdCx s.T.Z σ) W → ∀ T : Set Y, IsClosed T → (∀ y : CxPts q (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F)), up jm hq σ y ∈ ptsOf s.T.Z W → y.1 (IsLocalRing.closedPoint ℂ) ∈ T) → ∃ v ∈ T, jm v ∉ abLocus s.T.Z.t.G ∧ CharZero (Y.residueField v) ∧ Order.coheight v = 1 := by
  first | exact @GlobalTheory.HorComp.exists_coheight_eq_one_of_maximal | exact GlobalTheory.HorComp.exists_coheight_eq_one_of_maximal | (intros; apply GlobalTheory.HorComp.exists_coheight_eq_one_of_maximal <;> assumption)
