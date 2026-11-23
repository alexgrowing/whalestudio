import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramChangeBlockDiagonalFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicFrameInChartTargetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicFrameCurvatureLimitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricChernCurvaturePullbackStatement
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
set_option autoImplicit false

namespace GlobalTheory.ArchLim

theorem ch2Dens_eq_eig : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (M : DRBase O c) (Y : Scheme.{0}) (i : Y ⟶ M.B) (hi : (i ≫ M.b) ≫ O.s.T.Z.s = i ≫ M.q) (σ : O.κ.c.F →+* ℂ) (e : ℕ) (ch : AlgChart (i ≫ M.q) (σ.comp _) (e + 2)), ∀ y ∈ ch.e.source, ∃ (U : Set (V (e + 2))) (a : V (e + 2) → CxFr O.s.T.Z σ), IsOpen U ∧ ch.e y ∈ U ∧ HolFam U a ∧ ContinuousOn (fun u => (a u).1) U ∧ (∀ u ∈ U, (a u).1 = up (i ≫ M.b) hi σ (ch.e.symm u)) ∧ ∀ R : ℝ, (∀ τ, IsPosFrame U (eigGram (M.x.eigMetAt σ (some R)) a τ)) ∧ secondChernDensityOfMetric ((((M.h R).pull M.b rfl).pull i rfl).met _) (((M.lam R).pull i rfl).φ _) e ch y = secondChernDensity e (fun ξ₁ η₁ ξ₂ η₂ => ∑ τ, chTwo (eigGram (M.x.eigMetAt σ (some R)) a τ) (ch.e y) ξ₁ η₁ ξ₂ η₂) (Matrix.of fun a' b' => -∑ τ, (curv (eigGram (M.x.eigMetAt σ (some R)) a τ) (ch.e y) (bas _ a') (bas _ b')).trace) := by
  intro D O c M Y i hi σ e ch y hy
  obtain ⟨U, a, hU, hyU, hUt, hHol, hcont, hup, hpos⟩ := GlobalTheory.T.holomorphic_frame_in_chart_target D O c M Y i hi σ e ch y hy
  let cE := (((((M.h 0).pull M.b rfl).pull i rfl).met (σ.comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F))).isVB.pick y)
  obtain ⟨T, hTd, hTu, hG⟩ := GlobalTheory.T.holomorphic_frame_curvature_limit D O c M Y i hi σ e ch cE U a hU hUt hHol hcont hup
  refine ⟨U, a, hU, hyU, hHol, hcont, hup, fun R => ⟨hpos R, ?_⟩⟩
  have hyE : y ∈ ptsIn _ _ cE.U := VB.IsVB.mem_pick _ y
  have hW : IsOpen (U ∩ ch.e.symm ⁻¹' ptsIn _ _ cE.U) :=
    (ch.e.continuousOn_symm.mono hUt).isOpen_inter_preimage hU (isOpen_ptsIn _)
  have hyW : ch.e y ∈ U ∩ ch.e.symm ⁻¹' ptsIn _ _ cE.U :=
    ⟨hyU, by rw [Set.mem_preimage, ch.e.left_inv hy]; exact hyE⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.T.gram_change_block_diagonal_frame (e + 2) (D.host.E →+* ℂ) (fun τ => O.S.Dw.mult τ) (Fin (D.R.f * O.N)) _
    (fun τ => eigGram (M.x.eigMetAt σ (some R)) a τ) T
    (fun u => ((((M.h R).pull M.b rfl).pull i rfl).met (σ.comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F))).G cE (ch.e.symm u)) hW
    (fun τ => ⟨hW, fun a b => ((hpos R τ).smooth a b).mono Set.inter_subset_left,
      fun z hz => (hpos R τ).posDef z hz.1⟩) hTd hTu (hG R) (ch.e y) hyW
  have hC := GlobalTheory.T.det_metric_chern_curvature_pullback _ _ _ _ _ i rfl _ _ _ ((M.h R).pull M.b rfl) ((M.H R).pull M.b rfl) (e + 2) ch cE y hy hyE
  have key : secondChernDensityOfMetric ((((M.h R).pull M.b rfl).pull i rfl).met _) (((M.lam R).pull i rfl).φ _) e ch y =
      secondChernDensity e (chTwo (fun u => ((((M.h R).pull M.b rfl).pull i rfl).met (σ.comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F))).G cE (ch.e.symm u)) (ch.e y))
        (chernMat (((VMetric.det ((M.H R).pull M.b rfl)).pull i rfl).φ (σ.comp (algebraMap (𝓞 O.κ.c.F) O.κ.c.F))) ch y) := rfl
  rw [key, h1, hC]
  congr 1
  ext a' b'
  simp only [Matrix.of_apply, h2]

end GlobalTheory.ArchLim
