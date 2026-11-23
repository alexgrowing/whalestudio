import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity

set_option autoImplicit false

noncomputable section

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

namespace GlobalTheory.BdFamily

theorem contDiffAt_comp {K : Type} [CommRing K] {Y : Scheme.{0}} {p : Y ⟶ Sp K} {σ : K →+* ℂ} {d : ℕ}
    (R : AnRead p σ d) {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] {B : Set W}
    (hB : IsOpen B) {y : W → CxPts p σ} (hy : IsHolTo B fun b => (y b).1) (hcont : ContinuousOn y B)
    {O : Set (CxPts p σ)} (hO : IsOpen O) {φ : CxPts p σ → ℝ} (hφ : R.SmoothOn O φ) {b : W} (hb : b ∈ B)
    (hbO : y b ∈ O) : ContDiffAt ℝ ∞ (fun v => φ (y v)) b := by
  have hdU : ∀ (U : Y.Opens) (f : Γ(Y, U)), DifferentiableOn ℂ (fun b => ev p σ U f (y b))
      {b ∈ B | y b ∈ ptsIn p σ U} := fun U f => (hy U f).2
  obtain ⟨i, hc⟩ := R.cover (y b)
  set c := R.chart i with hcdef
  have hOc : IsOpen {b ∈ B | y b ∈ c.e.source} := hcont.isOpen_inter_preimage hB c.e.open_source
  have hdiff : DifferentiableOn ℂ (fun b => c.e (y b)) {b ∈ B | y b ∈ c.e.source} :=
    differentiableOn_euclidean.2 fun a => ((hdU c.U (c.x a)).mono
      fun v hv => ⟨hv.1, c.source_subset hv.2⟩).congr fun v hv => c.apply_eq _ hv.2 a
  have hb' : b ∈ {b ∈ B | y b ∈ c.e.source} := ⟨hb, hc⟩
  have hF : ContDiffAt ℝ ∞ (fun b => c.e (y b)) b :=
    (GlobalTheory.SCV.contDiffAt_of_differentiableOn hdiff (hOc.mem_nhds hb') _).restrict_scalars ℝ
  have hφc : ContDiffAt ℝ ∞ (φ ∘ c.e.symm) (c.e (y b)) :=
    (hφ.chart hO c).contDiffAt ((GlobalTheory.ChartGlue.isOpen_over c.e hO).mem_nhds (GlobalTheory.ChartGlue.mem_over c.e hc hbO))
  refine (hφc.comp b hF).congr_of_eventuallyEq ?_
  filter_upwards [hOc.mem_nhds hb'] with w hw
  simp only [Function.comp_apply, c.e.left_inv hw.2]

theorem contDiffAt_r : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s)
    (σ : κ.c.F →+* ℂ) (n : ℕ) (U : Set (V n)) (y : V n → CxPts (genStr s.T.Z) σ), IsOpen U →
    IsHolTo U (fun b => (y b).1) → ContinuousOn y U → ∀ u ∈ U, ¬ LiesIn (y u) (genBd s.T.Z) →
    ContDiffAt ℝ (∞ : WithTop ℕ∞) (fun v => x.r σ (y v)) u := by
  intro D A N j S κ s x σ n U y hU hy hc u hu hb
  have h1 : ∀ i, ContDiffAt ℝ ∞ (fun v => Real.log (x.nrm σ i (y v) ^ 2)) u := fun i =>
    contDiffAt_comp _ hU hy hc (isOpen_not_liesIn _) (x.nrm_div σ i).smoothOn_log hu
      fun h => hb ((x.liesIn_genBd_iff _).2 ⟨i, h⟩)
  refine ((contDiffAt_const (c := Real.exp 1)).sub (ContDiffAt.sum (s := Finset.univ) fun i _ => h1 i)).congr_of_eventuallyEq ?_
  filter_upwards [(hc.continuousAt (hU.mem_nhds hu)).eventually ((isOpen_not_liesIn _).mem_nhds hb)] with v hv
  rw [OddPrimesWithRootsOfUnity.r, ← Finset.prod_pow, Real.log_prod fun i _ => (pow_pos (x.nrm_pos hv i) 2).ne']

end GlobalTheory.BdFamily

end
