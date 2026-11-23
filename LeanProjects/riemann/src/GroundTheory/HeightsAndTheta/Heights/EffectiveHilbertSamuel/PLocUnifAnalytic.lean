import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsLocUnifAnalytic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open Set Filter Topology Complex MeasureTheory Metric
open scoped Real

namespace LocUnifAnalyticProof

theorem norm_torusMap_sub {D : ℕ} (c : Fin D → ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : Fin D → ℝ)
    (j : Fin D) : ‖torusMap c (fun _ => r) θ j - c j‖ = r := by
  simp [torusMap, abs_of_nonneg hr]

theorem continuous_torusMap' {D : ℕ} (c : Fin D → ℂ) (R : Fin D → ℝ) :
    Continuous (torusMap c R) := by
  unfold torusMap; fun_prop

theorem cauchy_polydisc : ∀ (D : ℕ) (g : (Fin D → ℂ) → ℂ) (c : Fin D → ℂ) (r : ℝ),
    ContinuousOn g {w | ∀ j, ‖w j - c j‖ ≤ r} →
    (∀ w ∈ {w : Fin D → ℂ | ∀ j, ‖w j - c j‖ ≤ r}, ∀ j,
      DifferentiableAt ℂ (fun t => g (Function.update w j t)) (w j)) →
    ∀ z : Fin D → ℂ, (∀ j, ‖z j - c j‖ < r) →
      (2 * π * I) ^ D * g z = ∯ w in T(c, fun _ => r), (∏ j, (w j - z j)⁻¹) * g w
  | 0, g, c, r, _, _, z, _ => by
    simp [Subsingleton.elim z c]
  | D + 1, g, c, r, hc, hd, z, hz => by
    have hr : 0 < r := lt_of_le_of_lt (norm_nonneg _) (hz 0)
    have mem : ∀ (t : ℂ) (y : Fin D → ℂ), ‖t - c 0‖ ≤ r → (∀ j, ‖y j - c (Fin.succ j)‖ ≤ r) →
        (Fin.cons t y : Fin (D + 1) → ℂ) ∈ {w : Fin (D + 1) → ℂ | ∀ j, ‖w j - c j‖ ≤ r} := by
      intro t y ht hy j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa using ht
      · simpa using hy j
    have h1 : DifferentiableOn ℂ (fun t => g (Fin.cons t (Fin.tail z))) (closedBall (c 0) r) := by
      intro t ht
      have hm := mem t (Fin.tail z) (by simpa [dist_eq_norm] using ht)
        (fun j => (hz j.succ).le)
      have := hd _ hm 0
      simp only [Fin.update_cons_zero, Fin.cons_zero] at this
      exact this.differentiableWithinAt
    have hz0 : z 0 ∈ ball (c 0) r := by simpa [dist_eq_norm] using hz 0
    have hC := h1.circleIntegral_sub_inv_smul hz0
    have hin : ∀ x ∈ sphere (c 0) r,
        (∯ y in T(c ∘ Fin.succ, fun _ => r), (∏ j, (y j - Fin.tail z j)⁻¹) * g (Fin.cons x y))
          = (2 * π * I) ^ D * g (Fin.cons x (Fin.tail z)) := by
      intro x hx
      have hx' : ‖x - c 0‖ ≤ r := by
        rw [mem_sphere, dist_eq_norm] at hx; exact hx.le
      refine (cauchy_polydisc D (fun y => g (Fin.cons x y)) (c ∘ Fin.succ) r ?_ ?_
        (Fin.tail z) ?_).symm
      · have hcons : Continuous (fun y : Fin D → ℂ => (Fin.cons x y : Fin (D + 1) → ℂ)) :=
          continuous_const.finCons continuous_id
        refine hc.comp hcons.continuousOn ?_
        intro y hy; exact mem x y hx' hy
      · intro y hy j
        have := hd _ (mem x y hx' hy) j.succ
        simpa [Fin.cons_update] using this
      · intro j; exact hz j.succ
    have hint : TorusIntegrable (fun w : Fin (D + 1) → ℂ => (∏ j, (w j - z j)⁻¹) * g w) c
        (fun _ => r) := by
      have hcont : Continuous (fun θ : Fin (D + 1) → ℝ =>
          (∏ j, (torusMap c (fun _ => r) θ j - z j)⁻¹) * g (torusMap c (fun _ => r) θ)) := by
        refine Continuous.mul ?_ ?_
        · refine continuous_finsetProd _ fun j _ => ?_
          have hj : Continuous fun θ : Fin (D + 1) → ℝ => torusMap c (fun _ => r) θ j - z j := by
            unfold torusMap; fun_prop
          refine hj.inv₀ fun θ h => ?_
          have h2 := norm_torusMap_sub c hr.le θ j
          rw [sub_eq_zero] at h
          rw [h] at h2
          linarith [hz j]
        · exact hc.comp_continuous (continuous_torusMap' c _)
            fun θ j => (norm_torusMap_sub c hr.le θ j).le
      exact hcont.continuousOn.integrableOn_compact isCompact_Icc
    calc (2 * π * I) ^ (D + 1) * g z
        = (2 * π * I) ^ D * ∮ x in C(c 0, r), (x - z 0)⁻¹ • g (Fin.cons x (Fin.tail z)) := by
          rw [hC, smul_eq_mul, Fin.cons_self_tail]; ring
      _ = ∮ x in C(c 0, r), (x - z 0)⁻¹ * ∯ y in T(c ∘ Fin.succ, fun _ => r),
            (∏ j, (y j - Fin.tail z j)⁻¹) * g (Fin.cons x y) := by
          rw [← circleIntegral.integral_const_mul]
          refine circleIntegral.integral_congr hr.le fun x hx => ?_
          simp only [smul_eq_mul]
          rw [hin x hx]; ring
      _ = _ := by
          rw [torusIntegral_succ hint]
          congr 1
          funext x
          rw [← torusIntegral_const_mul]
          congr 1
          funext y
          simp [Fin.prod_univ_succ, Fin.tail]
          ring

def torusSet {D : ℕ} (c : Fin D → ℂ) (r : ℝ) : Set (Fin D → ℂ) :=
  Set.pi univ fun j => sphere (c j) r

instance {D : ℕ} (c : Fin D → ℂ) (r : ℝ) : CompactSpace (torusSet c r) :=
  isCompact_iff_compactSpace.mp (isCompact_univ_pi fun _ => isCompact_sphere _ _)

theorem torusMap_mem {D : ℕ} (c : Fin D → ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : Fin D → ℝ) :
    torusMap c (fun _ => r) θ ∈ torusSet c r := fun j _ => by
  rw [mem_sphere, dist_eq_norm]; exact norm_torusMap_sub c hr θ j

theorem continuous_torusMap_comp {D : ℕ} (c : Fin D → ℂ) {r : ℝ} (hr : 0 ≤ r)
    (κ : C(torusSet c r, ℂ)) :
    Continuous fun θ : Fin D → ℝ => κ ⟨torusMap c (fun _ => r) θ, torusMap_mem c hr θ⟩ :=
  κ.continuous.comp ((continuous_torusMap' c _).subtype_mk _)

noncomputable def boxIntegral {D : ℕ} (c : Fin D → ℂ) {r : ℝ} (hr : 0 ≤ r) :
    C(torusSet c r, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun κ => ∫ θ in Icc (0 : Fin D → ℝ) (fun _ => 2 * π),
        κ ⟨torusMap c (fun _ => r) θ, torusMap_mem c hr θ⟩
      map_add' := fun κ μ => by
        simp only [ContinuousMap.add_apply]
        exact integral_add
          ((continuous_torusMap_comp c hr κ).continuousOn.integrableOn_compact isCompact_Icc)
          ((continuous_torusMap_comp c hr μ).continuousOn.integrableOn_compact isCompact_Icc)
      map_smul' := fun a κ => by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply]
        exact integral_smul a _ }
    (volume.real (Icc (0 : Fin D → ℝ) fun _ => 2 * π))
    (fun κ => (norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure (Fin D → ℝ)))
        measure_Icc_lt_top fun θ _ => κ.norm_coe_le_norm _).trans_eq (mul_comm _ _))

theorem boxIntegral_apply {D : ℕ} (c : Fin D → ℂ) {r : ℝ} (hr : 0 ≤ r) (κ : C(torusSet c r, ℂ)) :
    boxIntegral c hr κ = ∫ θ in Icc (0 : Fin D → ℝ) (fun _ => 2 * π),
        κ ⟨torusMap c (fun _ => r) θ, torusMap_mem c hr θ⟩ := rfl

theorem analyticAt_of_sep {D : ℕ} (g : (Fin D → ℂ) → ℂ) (c : Fin D → ℂ) {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn g {w | ∀ j, ‖w j - c j‖ ≤ r})
    (hd : ∀ w ∈ {w : Fin D → ℂ | ∀ j, ‖w j - c j‖ ≤ r}, ∀ j,
      DifferentiableAt ℂ (fun t => g (Function.update w j t)) (w j)) :
    AnalyticAt ℂ g c := by
  let ψ : Fin D → C(torusSet c r, ℂ) := fun j => ⟨fun w => (w : Fin D → ℂ) j,
    (continuous_apply j).comp continuous_subtype_val⟩
  let u : Fin D → (Fin D → ℂ) → C(torusSet c r, ℂ) :=
    fun j z => ψ j - algebraMap ℂ C(torusSet c r, ℂ) (z j)
  have hu_apply : ∀ j z (w : torusSet c r), u j z w = (w : Fin D → ℂ) j - z j := by
    intro j z w; simp [u, ψ]
  have hunit : ∀ z : Fin D → ℂ, (∀ j, ‖z j - c j‖ < r) → ∀ j, IsUnit (u j z) := by
    intro z hz j
    rw [ContinuousMap.isUnit_iff_forall_ne_zero]
    intro w h
    rw [hu_apply, sub_eq_zero] at h
    have hw := w.2 j (mem_univ _)
    rw [mem_sphere, dist_eq_norm, h] at hw
    linarith [hz j]
  have hinv_apply : ∀ z : Fin D → ℂ, (∀ j, ‖z j - c j‖ < r) → ∀ j (w : torusSet c r),
      Ring.inverse (u j z) w = ((w : Fin D → ℂ) j - z j)⁻¹ := by
    intro z hz j w
    obtain ⟨U, hU⟩ := hunit z hz j
    rw [← hu_apply, ← hU, Ring.inverse_unit]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← ContinuousMap.mul_apply, Units.inv_mul]
    rfl
  have hcT : ∀ w ∈ torusSet c r, w ∈ {w : Fin D → ℂ | ∀ j, ‖w j - c j‖ ≤ r} := by
    intro w hw j
    have := hw j (mem_univ _)
    rw [mem_sphere, dist_eq_norm] at this
    exact this.le
  let G : C(torusSet c r, ℂ) := ⟨fun w => (∏ j, ((w : Fin D → ℂ) j - c j) * I) * g w, by
    refine Continuous.mul (continuous_finsetProd _ fun j _ =>
      (((continuous_apply j).comp continuous_subtype_val).sub continuous_const).mul
        continuous_const) ?_
    exact hc.comp_continuous continuous_subtype_val fun w => hcT w w.2⟩
  have hc0 : ∀ j, ‖c j - c j‖ < r := fun j => by simpa using hr
  have han : AnalyticAt ℂ (fun z => (2 * π * I)⁻¹ ^ D *
      boxIntegral c hr.le ((∏ j, Ring.inverse (u j z)) * G)) c := by
    refine analyticAt_const.mul (((boxIntegral c hr.le).analyticAt _).comp ?_)
    refine AnalyticAt.mul ?_ analyticAt_const
    refine Finset.analyticAt_fun_prod _ fun j _ => ?_
    obtain ⟨U, hU⟩ := hunit c hc0 j
    have hlin : AnalyticAt ℂ (u j) c := by
      have h2 : AnalyticAt ℂ (fun z : Fin D → ℂ => algebraMap ℂ C(torusSet c r, ℂ) (z j)) c :=
        ((algebraMapCLM ℂ C(torusSet c r, ℂ)).comp
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin D => ℂ) j)).analyticAt c
      exact analyticAt_const.sub h2
    exact (analyticAt_inverse (𝕜 := ℂ) U).comp_of_eq hlin hU.symm
  refine han.congr ?_
  filter_upwards [ball_mem_nhds c hr] with z hz
  have hz' : ∀ j, ‖z j - c j‖ < r := by
    intro j
    rw [mem_ball, dist_eq_norm] at hz
    exact lt_of_le_of_lt (norm_le_pi_norm (z - c) j) hz
  have key := cauchy_polydisc D g c r hc hd z hz'
  have hT : boxIntegral c hr.le ((∏ j, Ring.inverse (u j z)) * G) =
      ∯ w in T(c, fun _ => r), (∏ j, (w j - z j)⁻¹) * g w := by
    rw [boxIntegral_apply, torusIntegral]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [ContinuousMap.mul_apply, ContinuousMap.prod_apply, hinv_apply z hz', smul_eq_mul]
    simp [G, torusMap]
    ring
  rw [hT, ← key, inv_pow, inv_mul_cancel_left₀ (pow_ne_zero _ two_pi_I_ne_zero)]

theorem _root_.GroundTheory.Heights₂.Heights.EffectiveHS.LocUnifAnalytic.proof :
    LocUnifAnalytic.Statement := by
  intro D V f g hV hf hlim c hc
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV c hc
  have hr : 0 < ε / 2 := half_pos hε
  have hsub : {w : Fin D → ℂ | ∀ j, ‖w j - c j‖ ≤ ε / 2} ⊆ V := by
    intro w hw
    apply hball
    rw [mem_ball]
    calc dist w c ≤ ε / 2 := (dist_pi_le_iff hr.le).2 fun j => by rw [dist_eq_norm]; exact hw j
      _ < ε := half_lt_self hε
  have hgc : ContinuousOn g V :=
    hlim.continuousOn (Frequently.of_forall fun n => (hf n).continuousOn)
  refine analyticAt_of_sep g c hr (hgc.mono hsub) fun w hw j => ?_
  have hwV := hsub hw
  let s : ℂ → (Fin D → ℂ) := fun t => Function.update w j t
  have hs : Continuous s := continuous_const.update j continuous_id
  have hS : IsOpen (s ⁻¹' V) := hV.preimage hs
  have hmem : w j ∈ s ⁻¹' V := by simpa [s] using hwV
  have hd : DifferentiableOn ℂ (g ∘ s) (s ⁻¹' V) := by
    refine (hlim.comp s (mapsTo_preimage s V) hs.continuousOn).differentiableOn ?_ hS
    refine Eventually.of_forall fun n t ht => ?_
    exact ((hf n (s t) ht).differentiableAt.comp t
      (hasFDerivAt_update (𝕜 := ℂ) w (i := j) t).differentiableAt).differentiableWithinAt
  exact hd.differentiableAt (hS.mem_nhds hmem)

end LocUnifAnalyticProof

end GroundTheory.Heights₂.Heights.EffectiveHS
