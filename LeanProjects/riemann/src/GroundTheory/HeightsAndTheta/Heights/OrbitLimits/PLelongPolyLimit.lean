import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StLelongPolyLimit
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StVarIntGraph
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StLocalMultComap
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StLelongWeightLimit
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology Matrix
open scoped ContDiff
open GroundTheory.Heights₂.Heights (varInt SmoothNear localMult linEval linForm linForm_single)
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)

theorem smoothNear_comp_init {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (p : MvPolynomial (Fin n) ℂ)
    {g : (Fin n → ℂ) → ℝ} (hg : SmoothNear (zeroSet J) g) :
    SmoothNear (zeroSet (graphIdeal J p)) (fun x => g (Fin.init x)) := by
  obtain ⟨U, hU, hJU, hgU⟩ := hg
  have hinit : ContDiff ℝ ∞ (fun x : Fin (n + 1) → ℂ => Fin.init x) :=
    contDiff_pi.2 fun i => contDiff_apply ℝ ℂ (Fin.castSucc i)
  exact ⟨(fun x => Fin.init x) ⁻¹' U, hU.preimage hinit.continuous,
    fun x hx => hJU (init_mem_zeroSet p hx), hgU.comp hinit.contDiffOn fun _ hx => hx⟩

theorem linEval_single_last {n : ℕ} (x : Fin (n + 1) → ℂ) :
    linEval (Pi.single (Fin.last n) 1) x = x (Fin.last n) := by
  simp [linEval, Pi.single_apply]

theorem LelongPolyLimit.proof (hGraph : VarIntGraph.Statement) (hMult : LocalMultComap.Statement)
    (hWeight : LelongWeightLimit.Statement) : LelongPolyLimit.Statement := by
  intro n d J p f k φ hJ hd hp hf hfc hφ hk hk0
  obtain ⟨R, hR⟩ := hfc.isCompact.exists_bound_of_continuousOn (MvPolynomial.continuous_eval p).continuousOn
  let χ : ContDiffBump (0 : ℂ) := ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩
  let F : (Fin (n + 1) → ℂ) → ℝ := fun x => f (Fin.init x) * χ (x (Fin.last n))
  let Φ : Fin d → (Fin (n + 1) → ℂ) → ℝ := fun j x => φ j (Fin.init x)
  let k' : (Fin (n + 1) → ℂ) → ℝ := fun x => k (Fin.init x)
  have hFγ : (fun x => F (graphPt p x)) = f := by
    funext x
    simp only [F, graphPt_init, graphPt_last]
    by_cases hx : x ∈ tsupport f
    · rw [χ.one_of_mem_closedBall, mul_one]
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hR x hx).trans (by show R ≤ |R| + 1; linarith [le_abs_self R])
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hΦγ : (fun j x => Φ j (graphPt p x)) = φ := by
    funext j x
    simp only [Φ, graphPt_init]
  have hF : SmoothNear (zeroSet (graphIdeal J p)) F := by
    obtain ⟨U, hU, hJU, hfU⟩ := smoothNear_comp_init p hf
    exact ⟨U, hU, hJU, hfU.mul ((χ.contDiff.comp (contDiff_apply ℝ ℂ (Fin.last n))).contDiffOn)⟩
  have hFc : HasCompactSupport F := by
    refine HasCompactSupport.intro ((hfc.isCompact.prod χ.hasCompactSupport.isCompact).image
      (Continuous.finSnoc (A := fun _ => ℂ) continuous_fst continuous_snd :
        Continuous fun q : (Fin n → ℂ) × ℂ => (Fin.snoc q.1 q.2 : Fin (n + 1) → ℂ))) fun x hx => ?_
    by_contra h
    exact hx ⟨(Fin.init x, x (Fin.last n)), ⟨subset_tsupport _ (left_ne_zero_of_mul h),
      subset_tsupport _ (right_ne_zero_of_mul h)⟩, Fin.snoc_init_self x⟩
  have hΦ : ∀ j, SmoothNear (zeroSet (graphIdeal J p)) (Φ j) := fun j => smoothNear_comp_init p (hφ j)
  have key := hWeight (n + 1) d (graphIdeal J p) (Pi.single (Fin.last n) 1) F k' Φ (graphIdeal_isPrime hJ p)
    ((ringKrullDim_graphIdeal J p).trans hd) (by rw [linForm_single]; exact X_last_not_mem_graphIdeal hp)
    hF hFc hΦ (smoothNear_comp_init p hk) (fun x hx => hk0 _ (init_mem_zeroSet p hx))
  simp only [linEval_single_last, linForm_single] at key
  rw [minimalPrimes_graphIdeal_sup, finsum_mem_image (graphIdeal_injective p).injOn] at key

  have hsum : ∀ W ∈ (J ⊔ Ideal.span {p}).minimalPrimes,
      (localMult (graphIdeal J p ⊔ Ideal.span {X (Fin.last n)}) (graphIdeal W p) : ℝ) * varInt (graphIdeal W p) d F Φ =
        (localMult (J ⊔ Ideal.span {p}) W : ℝ) * varInt W d f φ := by
    intro W hW
    have hWp : W.IsPrime := hW.1.1
    have hsub : zeroSet (graphIdeal W p) ⊆ zeroSet (graphIdeal J p) := fun x hx q hq =>
      hx q (graphIdeal_mono p (le_sup_left.trans hW.1.2) hq)
    have hm : localMult (graphIdeal (J ⊔ Ideal.span {p}) p) (graphIdeal W p) = localMult (J ⊔ Ideal.span {p}) W :=
      hMult _ _ (graphHom p).toRingHom _ _ (graphHom_surjective p) hWp
    have hv := hGraph n d W p F Φ hWp (let ⟨U, hU, hJU, hFU⟩ := hF; ⟨U, hU, hsub.trans hJU, hFU⟩)
      (fun j => let ⟨U, hU, hJU, hΦU⟩ := hΦ j; ⟨U, hU, hsub.trans hJU, hΦU⟩)
    rw [graphIdeal_sup_span, hm, hv, hFγ, hΦγ]
  rw [finsum_mem_congr rfl hsum] at key

  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  obtain ⟨U, hU, hJU, hkU⟩ := smoothNear_comp_init p hk
  have hG : SmoothNear (zeroSet (graphIdeal J p))
      (fun x => Real.log (‖x (Fin.last n)‖ ^ 2 + ε * k' x ^ 2) / 2) := by
    refine ⟨U ∩ k' ⁻¹' Set.Ioi 0, hkU.continuousOn.isOpen_inter_preimage hU isOpen_Ioi,
      fun x hx => ⟨hJU hx, hk0 _ (init_mem_zeroSet p hx)⟩, ?_⟩
    refine ContDiffOn.div_const (ContDiffOn.log ?_ fun x hx => ?_) _
    · exact ((contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ (Fin.last n))).contDiffOn.add
        (contDiffOn_const.mul ((hkU.mono Set.inter_subset_left).pow 2))
    · exact (add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hε (pow_pos hx.2 2))).ne'
  rw [hGraph n (d + 1) J p F _ hJ hF (fun j => Fin.cases hG hΦ j), hFγ]
  congr 1
  funext j x
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [graphPt_init, graphPt_last, k']
  · simp [Φ, graphPt_init]

end GroundTheory.Heights₂.Heights.Targets
