import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullFSExtension
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameBasePtFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CNormSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4 ProjLine
open scoped Topology

noncomputable section

namespace PullFSExtension

theorem leviForm_comp_clm {E F : Type} [Fintype E] [Fintype F] (L : (E → ℂ) →L[ℂ] (F → ℂ))
    (φ : (F → ℂ) → ℝ) (z w : E → ℂ) (hφ : ContDiffAt ℝ 2 φ (L z)) :
    leviForm (fun y => φ (L y)) z w = leviForm φ (L z) (L w) := by
  set Lr : (E → ℂ) →L[ℝ] (F → ℂ) := L.restrictScalars ℝ with hLr
  have hLr' : ∀ y, Lr y = L y := fun _ => rfl
  have hev : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 φ (L y) :=
    (L.continuous.tendsto z).eventually (hφ.eventually (by simp))
  have hfd : fderiv ℝ (fun y => φ (L y)) =ᶠ[𝓝 z]
      fun y => (ContinuousLinearMap.compL ℝ (E → ℂ) (F → ℂ) ℝ).flip Lr (fderiv ℝ φ (Lr y)) := by
    filter_upwards [hev] with y hy
    have h := (hy.differentiableAt (by norm_num)).hasFDerivAt.comp y Lr.hasFDerivAt
    exact h.fderiv
  have hd2 : DifferentiableAt ℝ (fderiv ℝ φ) (Lr z) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hD : HasFDerivAt
      (fun y => (ContinuousLinearMap.compL ℝ (E → ℂ) (F → ℂ) ℝ).flip Lr (fderiv ℝ φ (Lr y)))
      (((ContinuousLinearMap.compL ℝ (E → ℂ) (F → ℂ) ℝ).flip Lr).comp
        ((fderiv ℝ (fderiv ℝ φ) (Lr z)).comp Lr)) z :=
    ((ContinuousLinearMap.compL ℝ (E → ℂ) (F → ℂ) ℝ).flip Lr).hasFDerivAt.comp z
      (hd2.hasFDerivAt.comp z Lr.hasFDerivAt)
  unfold leviForm
  rw [hfd.fderiv_eq, hD.fderiv]
  have hI : Lr (Complex.I • w) = Complex.I • L w := by rw [hLr']; exact L.map_smul _ _
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, hI]
  rfl

theorem leviForm_congr {E : Type} [Fintype E] {φ ψ : (E → ℂ) → ℝ} {z : E → ℂ} (h : φ =ᶠ[𝓝 z] ψ)
    (w : E → ℂ) : leviForm φ z w = leviForm ψ z w := by
  have h1 : fderiv ℝ φ =ᶠ[𝓝 z] fderiv ℝ ψ := by
    filter_upwards [h.eventuallyEq_nhds] with y hy
    exact hy.fderiv_eq
  unfold leviForm
  rw [h1.fderiv_eq]

theorem normSqE_eq {J : Type} [Fintype J] (z : J → ℂ) : normSqE z = ∑ i, ‖z i‖ ^ 2 := by
  unfold normSqE
  rw [eL_apply, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

theorem normSqE_smul {J : Type} [Fintype J] (c : ℂ) (z : J → ℂ) :
    normSqE (c • z) = ‖c‖ ^ 2 * normSqE z := by
  simp only [normSqE_eq, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

theorem normSqE_conj {J : Type} [Fintype J] (z : J → ℂ) :
    normSqE (fun i => (starRingEnd ℂ) (z i)) = normSqE z := by
  simp only [normSqE_eq, Complex.norm_conj]

theorem normSqE_zero {J : Type} [Fintype J] : normSqE (0 : J → ℂ) = 0 := by
  simp [normSqE_eq]

theorem contDiff_normSqE {J : Type} [Fintype J] {n : WithTop ℕ∞} : ContDiff ℝ n (normSqE (J := J)) := by
  have : normSqE (J := J) = fun z => ‖eL z‖ ^ 2 := rfl
  rw [this]
  exact (contDiff_norm_sq ℝ).comp (eL (J := J)).contDiff

variable {κ : Type} [Fintype κ] {D : ℕ}

def pr (e : Fin (D + 1) → Ix κ) : (Ix κ → ℂ) →L[ℂ] (Fin (D + 1) → ℂ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (e k)

def ratio (e : Fin (D + 1) → Ix κ) (z : Ix κ → ℂ) : ℝ := normSqE (pr e z) / normSqE z

theorem ratio_smul (e : Fin (D + 1) → Ix κ) {c : ℂ} (hc : c ≠ 0) (z : Ix κ → ℂ) :
    ratio e (c • z) = ratio e z := by
  unfold ratio
  rw [map_smul, normSqE_smul, normSqE_smul]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hc))

theorem ratio_conj (e : Fin (D + 1) → Ix κ) (z : Ix κ → ℂ) :
    ratio e (fun i => (starRingEnd ℂ) (z i)) = ratio e z := by
  unfold ratio
  have : pr e (fun i => (starRingEnd ℂ) (z i)) = fun k => (starRingEnd ℂ) (pr e z k) := rfl
  rw [this, normSqE_conj, normSqE_conj]

theorem contDiffAt_ratio (e : Fin (D + 1) → Ix κ) {z : Ix κ → ℂ} (hz : z ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (ratio e) z :=
  (contDiff_normSqE.comp ((pr e).restrictScalars ℝ).contDiff).contDiffAt.div contDiff_normSqE.contDiffAt
    (normSqE_pos hz).ne'

def cut (δ t : ℝ) : ℝ := Real.smoothTransition ((t - δ / 4) / (δ / 4))

theorem cut_of_le {δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ δ / 4) : cut δ t = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

theorem cut_of_ge {δ t : ℝ} (hδ : 0 < δ) (ht : δ / 2 ≤ t) : cut δ t = 1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (by linarith)).mpr (by linarith))

def gfac (δ t : ℝ) : ℝ := Real.exp (cut δ t * Real.log t / 2)

theorem contDiff_gfac {δ : ℝ} (hδ : 0 < δ) {n : ℕ∞} : ContDiff ℝ n (gfac δ) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t < δ / 4
  · have : gfac δ =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      simp [gfac, cut_of_le hδ (le_of_lt hs)]
    exact contDiffAt_const.congr_of_eventuallyEq this
  · have ht0 : t ≠ 0 := by intro h; subst h; linarith
    have hcut : ContDiff ℝ n (cut δ) := by
      have : cut δ = Real.smoothTransition ∘ fun t => (t - δ / 4) / (δ / 4) := rfl
      rw [this]
      exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
    exact Real.contDiff_exp.contDiffAt.comp t
      (((hcut.contDiffAt.mul (Real.contDiffAt_log.mpr ht0))).div_const _)

theorem gfac_of_ge {δ t : ℝ} (hδ : 0 < δ) (ht : δ / 2 ≤ t) : gfac δ t = Real.sqrt t := by
  have ht0 : 0 < t := by linarith
  rw [gfac, cut_of_ge hδ ht, one_mul, ← Real.log_sqrt ht0.le, Real.exp_log (Real.sqrt_pos.mpr ht0)]

def metric (e : Fin (D + 1) → Ix κ) (δ : ℝ) : ConeMetric ℂ (Ix κ) where
  ρ z := Real.sqrt (normSqE z) * gfac δ (ratio e z)
  pos z hz := mul_pos (Real.sqrt_pos.mpr (normSqE_pos hz)) (Real.exp_pos _)
  smul c z := by
    by_cases hc : c = 0
    · subst hc
      simp [normSqE_zero]
    rw [ratio_smul e hc, normSqE_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), mul_assoc]

theorem metric_rho (e : Fin (D + 1) → Ix κ) (δ : ℝ) (z : Ix κ → ℂ) :
    (metric e δ).ρ z = Real.sqrt (normSqE z) * gfac δ (ratio e z) := rfl

theorem metric_of_ge (e : Fin (D + 1) → Ix κ) {δ : ℝ} (hδ : 0 < δ) {z : Ix κ → ℂ} (hz : z ≠ 0)
    (hr : δ / 2 ≤ ratio e z) : (metric e δ).ρ z = Real.sqrt (normSqE (pr e z)) := by
  rw [metric_rho, gfac_of_ge hδ hr, ← Real.sqrt_mul (normSqE_pos hz).le, ratio,
    mul_div_cancel₀ _ (normSqE_pos hz).ne']

theorem isSmoothMetric_metric (e : Fin (D + 1) → Ix κ) {δ : ℝ} (hδ : 0 < δ) :
    IsSmoothMetric (metric e δ) := by
  intro z hz
  have hz' : z ≠ 0 := hz
  refine ContDiffAt.contDiffWithinAt ?_
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => Real.sqrt (normSqE y)) z :=
    contDiff_normSqE.contDiffAt.sqrt (normSqE_pos hz').ne'
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => gfac δ (ratio e y)) z :=
    (contDiff_gfac hδ).contDiffAt.comp z (contDiffAt_ratio e hz')
  exact h1.mul h2

theorem isConjInvariant_metric (e : Fin (D + 1) → Ix κ) (δ : ℝ) : IsConjInvariant (metric e δ) := by
  intro z
  rw [metric_rho, metric_rho, normSqE_conj, ratio_conj]

variable {Ω : Type} [Field Ω] [CharZero Ω] {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ}

theorem pr_ne_zero (hBP : ProjFrameBasePtFree.Statement) (hfr : IsProjFrame x e) {z : Ix κ → ℂ}
    (hz : z ∈ pts (coordIdeal ℤ x)) : pr e z ≠ 0 := by
  intro h0
  apply hz.1
  funext i
  obtain ⟨u, j⟩ := i
  cases u
  obtain ⟨N, hN⟩ := hBP D Ω κ x e hfr () (fun _ => j)
  set ψ : MvPolynomial (Ix κ) ℤ →+* ℂ := (eval z).comp (map (Int.castRingHom ℂ)) with hψ
  have hle : coordIdeal ℤ x ⊔ Ideal.span (Set.range fun k : Fin (D + 1) =>
      linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) ⟨(), k⟩) ≤ RingHom.ker ψ := by
    refine sup_le (fun f hf => RingHom.mem_ker.mpr (hz.2 f hf)) (Ideal.span_le.mpr ?_)
    rintro _ ⟨k, rfl⟩
    have hk : z (e k) = 0 := congrFun h0 k
    have he : (⟨(), (e k).2⟩ : Ix κ) = e k := rfl
    simp only [SetLike.mem_coe, RingHom.mem_ker, hψ, RingHom.comp_apply, linForm, map_sum, map_mul,
      map_C, map_X, eval_C, eval_X, projMat]
    simp only [eq_intCast, Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single (e k).2 (fun i _ hi => if_neg (Ne.symm hi))
      (fun h => absurd (Finset.mem_univ _) h), if_pos rfl, he]
    exact hk
  have h1 := hle hN
  rw [RingHom.mem_ker] at h1
  simp only [hψ, RingHom.comp_apply, map_pow, map_X, eval_X, Finset.univ_unique,
    Finset.prod_singleton] at h1
  exact eq_zero_of_pow_eq_zero h1

theorem ratio_pos (hBP : ProjFrameBasePtFree.Statement) (hfr : IsProjFrame x e) {z : Ix κ → ℂ}
    (hz : z ∈ pts (coordIdeal ℤ x)) : 0 < ratio e z :=
  div_pos (normSqE_pos (pr_ne_zero hBP hfr hz)) (normSqE_pos hz.1)

theorem exists_ratio_lb (hBP : ProjFrameBasePtFree.Statement) (hfr : IsProjFrame x e) :
    ∃ δ > 0, ∀ z ∈ pts (coordIdeal ℤ x), δ ≤ ratio e z := by
  set S : Set (Ix κ → ℂ) :=
    {z | (∀ f ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) f) = 0) ∧ normSqE z = 1} with hSdef
  have hSpts : ∀ z ∈ S, z ∈ pts (coordIdeal ℤ x) := fun z hz =>
    ⟨fun h0 => by
      have h1 := hz.2
      rw [h0, normSqE_zero] at h1
      exact zero_ne_one h1, hz.1⟩
  have hnorm : ∀ z ∈ pts (coordIdeal ℤ x), ∃ z' ∈ S, ratio e z' = ratio e z := by
    intro z hz
    have hq := normSqE_pos hz.1
    have hs := Real.sqrt_pos.mpr hq
    set c : ℂ := (((Real.sqrt (normSqE z))⁻¹ : ℝ) : ℂ) with hcdef
    have hcn : ‖c‖ = (Real.sqrt (normSqE z))⁻¹ := by
      rw [hcdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
    have hc : c ≠ 0 := by
      intro h
      rw [h, norm_zero] at hcn
      exact (inv_pos.mpr hs).ne' hcn.symm
    refine ⟨c • z, ⟨(smul_mem_pts_coord x hz hc).2, ?_⟩, ratio_smul e hc z⟩
    rw [normSqE_smul, hcn, inv_pow, Real.sq_sqrt hq.le, inv_mul_cancel₀ hq.ne']
  have hSc : IsCompact S := by
    apply Metric.isCompact_of_isClosed_isBounded
    · have hA : IsClosed
          {z : Ix κ → ℂ | ∀ f ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) f) = 0} := by
        have h : {z : Ix κ → ℂ | ∀ f ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) f) = 0} =
            ⋂ f ∈ coordIdeal ℤ x, {z | eval z (map (Int.castRingHom ℂ) f) = 0} := by
          ext z
          simp
        rw [h]
        exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval _) continuous_const
      exact hA.inter (isClosed_eq (contDiff_normSqE (n := 0)).continuous continuous_const)
    · refine (Metric.isBounded_closedBall (x := (0 : Ix κ → ℂ)) (r := 1)).subset fun z hz => ?_
      rw [Metric.mem_closedBall, dist_zero_right]
      refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
      have h1 : ‖z i‖ ^ 2 ≤ 1 := by
        rw [← hz.2, normSqE_eq]
        exact Finset.single_le_sum (f := fun i => ‖z i‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      nlinarith [norm_nonneg (z i)]
  have hcont : ContinuousOn (ratio e) S := fun z hz =>
    (contDiffAt_ratio e (hSpts z hz).1 (n := 0)).continuousAt.continuousWithinAt
  rcases S.eq_empty_or_nonempty with hS | hS
  · refine ⟨1, one_pos, fun z hz => ?_⟩
    obtain ⟨z', hz', -⟩ := hnorm z hz
    rw [hS] at hz'
    simp at hz'
  · obtain ⟨z0, hz0, hmin⟩ := hSc.exists_isMinOn hS hcont
    refine ⟨ratio e z0, ratio_pos hBP hfr (hSpts z0 hz0), fun z hz => ?_⟩
    obtain ⟨z', hz', hr⟩ := hnorm z hz
    rw [← hr]
    exact hmin hz'

end PullFSExtension

open PullFSExtension in

theorem PullFSExtension.proof (hBP : ProjFrameBasePtFree.Statement) : PullFSExtension.Statement := by
  intro D Ω _ _ κ _ x e hfr
  obtain ⟨δ, hδ, hlb⟩ := exists_ratio_lb hBP hfr
  have hsm := isSmoothMetric_metric e hδ
  refine ⟨metric e δ, hsm, isConjInvariant_metric e δ, ⟨?_, ?_⟩, ?_⟩
  · refine hsm.mono fun z hz => ?_
    obtain ⟨i, hi⟩ := hz ()
    exact fun h0 => hi (congrFun h0 _)
  · intro z hz w _
    have hzp : z ∈ pts (coordIdeal ℤ x) :=
      ⟨fun h0 => by obtain ⟨i, hi⟩ := hz.1 (); exact hi (congrFun h0 _), hz.2⟩
    have hpz := pr_ne_zero hBP hfr hzp
    have hev : (fun y => Real.log ((HermLine.ofCone (metric e δ)).h y)) =ᶠ[𝓝 z]
        fun y => Real.log ((fsMetric (Fin (D + 1))).ρ (pr e y)) := by
      have hr : ∀ᶠ y in 𝓝 z, δ / 2 < ratio e y :=
        (contDiffAt_ratio e hzp.1 (n := 0)).continuousAt.eventually
          (lt_mem_nhds (by linarith [hlb z hzp]))
      filter_upwards [hr, isOpen_ne.mem_nhds hzp.1] with y hy hy0
      change Real.log ((metric e δ).ρ y) = _
      rw [metric_of_ge e hδ hy0 hy.le, congrFun log_fs_eq (pr e y),
        Real.log_sqrt (by rw [normSqE_eq]; positivity)]
      ring
    have hφ : ContDiffAt ℝ 2 (fun u => Real.log ((fsMetric (Fin (D + 1))).ρ u)) (pr e z) := by
      rw [log_fs_eq]
      exact contDiffAt_const.mul (contDiff_normSqE.contDiffAt.log (normSqE_pos hpz).ne')
    have key := leviForm_comp_clm (pr e) (fun u => Real.log ((fsMetric (Fin (D + 1))).ρ u)) z w hφ
    beta_reduce at key
    rw [leviForm_congr hev w, key]
    exact leviForm_log_fs_nonneg hpz (pr e w)
  · intro z hz
    rw [metric_of_ge e hδ hz.1 (by linarith [hlb z hz]), normSqE_eq]
    rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
