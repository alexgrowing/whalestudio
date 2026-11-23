import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenGramSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryDistanceSmoothInteriorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMixCurvatureLimitStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricSmoothOffBoundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulPowLeRpow
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

theorem GlobalTheory.ArchLim.tendsto_curv_eigMetAt : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) (n : ℕ) (U : Set (V n)) (a : V n → CxFr s.T.Z σ), IsOpen U → HolFam U a → ContinuousOn (fun u => (a u).1) U → ∀ u ∈ U, Inner (a u).1 → ∀ (τ : D.host.E →+* ℂ) (ξ η : V n), Tendsto (fun R : ℝ => curv (eigGram (x.eigMetAt σ (some R)) a τ) u ξ η) atTop (𝓝 (curv (eigGram (x.hodge σ) a τ) u ξ η)) := by
  intro D A N j S κ s x σ n U a hU hF hc u hu hin τ ξ η
  have hin' : ¬ LiesIn (a u).1 (genBd s.T.Z) := hin
  have h2 : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
  set H₀ := eigGram (x.eigMet σ) a τ with hH₀
  set H := eigGram (x.hodge σ) a τ with hH
  have s0 : ∀ i k, ContDiffAt ℝ 2 (fun v => H₀ v i k) u := fun i k =>
    (GlobalTheory.T.eigen_gram_smooth D A N j S κ s σ _ Set.univ isOpen_univ (x.smoothOn_eigMet σ) n U a hU hF hc u hu trivial τ i k).of_le h2
  have s1 : ∀ i k, ContDiffAt ℝ 2 (fun v => H v i k) u := fun i k =>
    (GlobalTheory.T.eigen_gram_smooth D A N j S κ s σ _ _ (isOpen_not_liesIn _) (ToroidalCompactificationData.hodge_smoothOn D A N j S κ s x σ) n U a hU hF hc u hu
      hin' τ i k).of_le h2
  have sr : ContDiffAt ℝ 2 (fun v => x.r σ (a v).1) u :=
    (GlobalTheory.T.boundary_distance_smooth_interior D A N j S κ s x σ n U (fun v => (a v).1) hU hF.1 hc u hu hin').of_le h2
  have hκ : 0 < x.kap := by
    have := (x.isMuExp_muExp (ToroidalCompactificationData.exists_isMuExp x)).1
    unfold ToroidalCompactificationData.kap; linarith
  have hru : 0 < x.r σ (a u).1 := (Real.exp_pos 1).trans_le (x.exp_le_r σ _)
  have sρ : ContDiffAt ℝ 2 (fun v => x.r σ (a v).1 ^ x.kap) u := sr.rpow_const_of_ne hru.ne'
  have u0 : IsUnit (H₀ u).det := by
    rw [hH₀, eigGram, det_transpose]; exact (isUnit_iff_isUnit_det _).1 ((x.eigMet σ).pos _ _ τ).isUnit
  have u1 : IsUnit (H u).det := by
    rw [hH, eigGram, det_transpose]; exact (isUnit_iff_isUnit_det _).1 ((x.hodge σ).pos _ _ τ).isUnit
  obtain ⟨L1, L2⟩ := GlobalTheory.T.graded_mix_curvature_limit H₀ H _ u s0 s1 sρ u0 u1 ξ η
  have hev : ∀ᶠ v in 𝓝 u, ¬ LiesIn (a v).1 (genBd s.T.Z) ∧ x.r σ (a v).1 < x.r σ (a u).1 + 1 :=
    Filter.Eventually.and (show ∀ᶠ v in 𝓝 u, ¬ LiesIn (a v).1 (genBd s.T.Z) from
      (hc.continuousAt (hU.mem_nhds hu)).preimage_mem_nhds ((isOpen_not_liesIn _).mem_nhds hin'))
      (sr.continuousAt.eventually (gt_mem_nhds (lt_add_one _)))
  have hw : ∀ R : ℝ, 2 ≤ R → x.r σ (a u).1 + 1 ≤ R ^ 2 → ∀ v, ¬ LiesIn (a v).1 (genBd s.T.Z) ∧
      x.r σ (a v).1 < x.r σ (a u).1 + 1 → x.wt σ R (a v).1 = 1 / (1 + R ^ (-x.kap) * x.r σ (a v).1 ^ x.kap) := by
    intro R hR hR2 v hv
    have hrv : 0 < x.r σ (a v).1 := (Real.exp_pos 1).trans_le (x.exp_le_r σ _)
    rw [x.wt_eq hR hv.1, cutWt_of_le _ hR hrv (hv.2.le.trans hR2), Real.div_rpow hrv.le (by linarith),
      Real.rpow_neg (by linarith)]
    ring
  have hRe : ∀ᶠ R : ℝ in atTop, 2 ≤ R ∧ x.r σ (a u).1 + 1 ≤ R ^ 2 := by
    filter_upwards [eventually_ge_atTop (max 2 (x.r σ (a u).1 + 1))] with R hR
    have h1 := le_of_max_le_left hR
    have h2 := le_of_max_le_right hR
    exact ⟨h1, by nlinarith⟩
  have hc0 := tendsto_rpow_neg_atTop hκ
  by_cases hτ : τ (A.H.rt : D.host.E) = A.H.rt0
  · refine (L1.comp hc0).congr' ?_
    filter_upwards [hRe] with R hR
    simp only [Function.comp_apply]
    refine curv_congr (hev.mono fun v hv => ?_) ξ η
    rw [eigGram, ToroidalCompactificationData.eigMetAt, EigMet.interp_gram _ hτ, hw R hR.1 hR.2 v hv, hH₀, hH, eigGram, eigGram]
    simp only [GlobalTheory.GradedNorm.mix, transpose_add, transpose_smul]
  · refine (L2.comp hc0).congr' ?_
    filter_upwards [hRe] with R hR
    simp only [Function.comp_apply]
    refine curv_congr (hev.mono fun v hv => ?_) ξ η
    rw [eigGram, ToroidalCompactificationData.eigMetAt]
    simp only [EigMet.interp, if_neg hτ]
    rw [hw R hR.1 hR.2 v hv, hH₀, hH, eigGram, eigGram]
    simp only [GlobalTheory.GradedNorm.mixDual, GlobalTheory.GradedNorm.mix, GlobalTheory.HermFrame.dualGram, GlobalTheory.LieMet.dualGram,
      transpose_add, transpose_smul, transpose_nonsing_inv, transpose_transpose]
