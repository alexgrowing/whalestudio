import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSupBoundBlock
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergman
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionPullback
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNonvanishingDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology

noncomputable section

section Invariance

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem SupBoundBlock.eval_torus_blockDeg {f : MRing ι} {k₀ : K} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n))
    (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * z p) (map (Int.castRingHom ℂ) f) =
      c k₀ ^ n * eval z (map (Int.castRingHom ℂ) f) := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hf m (support_map_subset _ _ hm)
  have hc : ∏ p : (Σ k, ι k), c p.1 ^ m p = c k₀ ^ n := by
    rw [Fintype.prod_sigma]
    simp_rw [Finset.prod_pow_eq_pow_sum, hdeg]
    rw [Fintype.prod_eq_single k₀ fun k hk => by simp [blockDeg, hk]]
    simp [blockDeg]
  simp_rw [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem SupBoundBlock.normRatio_torus {f : MRing ι} {k₀ : K} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n)) (A : HermLine ι)
    (hA : A.a = unitDeg k₀) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    ‖eval z (map (Int.castRingHom ℂ) f)‖ / A.h z ^ n = ‖eval z' (map (Int.castRingHom ℂ) f)‖ / A.h z' ^ n := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [SupBoundBlock.eval_torus_blockDeg hf, A.smul c z' hc, hA]
  have hprod : ∏ k, ‖c k‖ ^ unitDeg k₀ k = ‖c k₀‖ := by
    rw [Fintype.prod_eq_single k₀ fun k hk => by simp [unitDeg, hk]]
    simp [unitDeg]
  rw [hprod, norm_mul, norm_pow, mul_pow]
  have : ‖c k₀‖ ^ n ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 (hc k₀))
  rw [mul_div_mul_left _ _ this]

omit [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem SupBoundBlock.isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

end Invariance

theorem SupBoundBlock.proof (hS : SupNormAgainstL2.Statement) (hR : ResolutionPullback.Statement)
    (hN : NonvanishingDense.Statement) : SupBoundBlock.Statement := by
  intro D K _ _ ι _ Ω _ _ d
  obtain ⟨A, L, W, dV, -, hW, hμ, hsec⟩ := hR D K ι Ω d
  obtain ⟨⟨C, hC⟩, -⟩ := hS A L W dV hW
  refine ⟨max C 0 * Real.sqrt 2, fun n hn f hf z hz => ?_⟩
  set g : ((Σ k, ι k) → ℂ) → ℝ := fun w => ‖eval w (map (Int.castRingHom ℂ) f)‖ / d.A.h w ^ n with hg
  set M := max C 0 * Real.sqrt 2 * (n : ℝ) ^ ((D : ℝ) / 2) * blockL2Norm d n f with hM
  obtain ⟨s, hs, hps⟩ := hsec n f hf

  have hL2 : Real.sqrt (sectionL2NormSq W dV n s) ≤ Real.sqrt 2 * blockL2Norm d n f := by
    have hI : sectionL2NormSq W dV n s = ∫ x, g (blockPt d x) ^ 2 ∂d.dV := by
      rw [sectionL2NormSq, hμ]
      exact integral_congr_ae (Eventually.of_forall hps)
    have h2 : 0 ≤ ∫ x, (‖eval (conjPt (blockPt d x)) (map (Int.castRingHom ℂ) f)‖ /
        d.A.h (conjPt (blockPt d x)) ^ n) ^ 2 ∂d.dV := integral_nonneg fun _ => sq_nonneg _
    rw [hI, blockL2Norm, ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    linarith
  have hpow : Real.sqrt ((n : ℝ) ^ D) = (n : ℝ) ^ ((D : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    ring_nf

  have hres : ∀ x, g (blockPt d x) ≤ M := by
    intro x
    have h1 : g (blockPt d x) ≤ Real.sqrt (ptNormSq W n s x) := by
      rw [hps x, Real.sqrt_sq_eq_abs]
      exact le_abs_self _
    have h3 := hC n hn s hs x
    rw [hpow] at h3
    have ha : 0 ≤ (n : ℝ) ^ ((D : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    calc g (blockPt d x) ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * Real.sqrt (sectionL2NormSq W dV n s) := h1.trans h3
      _ ≤ max C 0 * (n : ℝ) ^ ((D : ℝ) / 2) * Real.sqrt (sectionL2NormSq W dV n s) := by
          gcongr
          exact le_max_left _ _
      _ ≤ max C 0 * (n : ℝ) ^ ((D : ℝ) / 2) * (Real.sqrt 2 * blockL2Norm d n f) := by
          gcongr
      _ = M := by rw [hM]; ring

  have hoff : ∀ w ∈ mcPts (mCoordIdeal d.y), w ∉ mcPts d.J → g w ≤ M := by
    intro w hw hwJ
    obtain ⟨x, hx⟩ := d.R.surj w hw hwJ
    calc g w = g (blockPt d x) := (SupBoundBlock.normRatio_torus hf d.A d.deg hx).symm
      _ ≤ M := hres x

  obtain ⟨F, hFJ, hFP⟩ := SetLike.not_le_iff_exists.1 d.R.nondeg
  set S := {w | w ∈ mcPts (mCoordIdeal d.y) ∧ eval w (map (Int.castRingHom ℂ) F) ≠ 0} with hSdef
  have hcl : z ∈ closure S := hN K ι (mCoordIdeal d.y) (D + 1) F d.arith hFP hz
  have hSM : ∀ w ∈ S, g w ≤ M := fun w hw => hoff w hw.1 fun hJ => hw.2 (hJ.2 F hFJ)
  have hcont : ContinuousAt g z := by
    have hh : ContinuousAt d.A.h z :=
      d.semipos.1.continuousOn.continuousAt (SupBoundBlock.isOpen_blockNonzero.mem_nhds hz.1)
    exact (continuous_norm.comp (MvPolynomial.continuous_eval _)).continuousAt.div (hh.pow n)
      (pow_ne_zero _ (d.A.pos z hz.1).ne')
  have := mem_closure_iff_nhdsWithin_neBot.1 hcl
  exact le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) (eventually_nhdsWithin_of_forall hSM)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
