import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraRegularity
import GroundTheory.AutomorphicForms.DixmierMalliavinBasic

namespace GroundTheory.Automorphic

open Sobolev Set Filter Topology MeasureTheory
open scoped ContDiff Manifold

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

theorem exists_kernel_eq_conv_of_aeval_laplacian [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] {ι : Type*} [Fintype ι]
    (bL : Module.Basis ι ℝ h.lieSubalgebra) (P : Polynomial ℂ) (hP : P.Monic) (hPd : 0 < P.natDegree)
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ κ : G → ℂ, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) ∧ HasCompactSupport κ ∧
      tsupport κ ⊆ U ∧ ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (h.laplacian bL) P f = 0 →
        ∀ g : G, (f : G → ℂ) g = ∫ y, (f : G → ℂ) (g * y) * κ y ∂μ := by
  let _ := h.chartedSpace
  set b := Module.finBasis ℝ 𝔤
  set d := Module.finrank ℝ 𝔤
  have hfc : ∀ f : h.smoothFuns (F := ℂ), ∀ g : G, Continuous fun y : G => (f : G → ℂ) (g * y) :=
    fun f g => (show h.IsSmoothFun (f : G → ℂ) from f.2).continuous.comp
      (continuous_const.mul continuous_id)
  have hexpc : Continuous fun x : EuclideanSpace ℝ (Fin d) => h.expG (coordEquiv b x) :=
    h.continuous_expG.comp (coordEquiv b).continuous
  obtain ⟨ε, hε, hdens⟩ := h.exists_smooth_density_expCoord μ b
  have hV : {x : EuclideanSpace ℝ (Fin d) | h.expG (coordEquiv b x) ∈ U} ∈ 𝓝 0 := by
    refine hexpc.continuousAt.preimage_mem_nhds ?_
    simpa using hU
  obtain ⟨ρ₀, hρ₀, hρ₀V⟩ := Metric.mem_nhds_iff.1 hV
  rcases Nat.eq_zero_or_pos d with hd | hd
  ·
    have hsub : ∀ x y : EuclideanSpace ℝ (Fin d), x = y := by
      intro x y; ext i; exact absurd i.2 (by omega)
    obtain ⟨κ, hκs, hκc, hκU, hκ⟩ := hdens (fun _ => 1) contDiff_const (fun x _ => by
      rw [hsub x 0]; exact Metric.mem_closedBall_self hε.le)
    refine ⟨κ, hκs, hκc, hκU.trans ?_, fun f _ g => ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact hρ₀V (by rw [hsub x 0]; exact Metric.mem_ball_self hρ₀)
    · have := hκ _ (hfc f g)
      simp_rw [mul_comm ((f : G → ℂ) _)]
      rw [this, integral_euclideanSpace_of_eq_zero hd]
      simp
  ·
    set Q := P ^ (d + 1)
    have hQ : Q.Monic := hP.pow _
    have hQd : Q.natDegree = (d + 1) * P.natDegree := hP.natDegree_pow _
    obtain ⟨δ, hδ, A, a, hA, ha, hell, hop⟩ := h.exists_elliptic_aeval_laplacian bL b Q hQ
    set ρ := min (min δ ε) ρ₀
    have hρ : 0 < ρ := lt_min (lt_min hδ hε) hρ₀
    have hρδ : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ Metric.ball 0 δ :=
      Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))
    have hρε : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ Metric.closedBall 0 ε :=
      Metric.ball_subset_closedBall.trans
        (Metric.closedBall_subset_closedBall ((min_le_left _ _).trans (min_le_right _ _)))
    have hρV : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ Metric.ball 0 ρ₀ :=
      Metric.ball_subset_ball (min_le_right _ _)
    have hm1 : 1 ≤ 2 * Q.natDegree := by rw [hQd]; nlinarith
    have hnm : d < 2 * (2 * Q.natDegree) := by rw [hQd]; nlinarith
    obtain ⟨E, β, -, -, hEs, -, hβs, -, hβU, hid⟩ := exists_parametrix hd hm1 hnm Metric.isOpen_ball
      hA (fun α hα => (ha α hα).contDiffOn Metric.isOpen_ball.uniqueDiffOn) hell Metric.isOpen_ball
      (Metric.mem_ball_self hρ) hρδ
    obtain ⟨κ, hκs, hκc, hκU, hκ⟩ := hdens β hβs (hβU.trans hρε)
    refine ⟨κ, hκs, hκc, hκU.trans ?_, fun f hf g => ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hρ₀V (hρV (hβU hx))
    · have hQf : Polynomial.aeval (h.laplacian bL) Q f = 0 := by
        rw [show Q = P ^ d * P from pow_succ P d, map_mul, Module.End.mul_apply, hf, map_zero]
      set ψ := fun y => (f : G → ℂ) (g * h.expG (coordEquiv b y))
      have hψ : ContDiff ℝ ∞ ψ := h.contDiff_comp_coordEquiv f.2 g b
      have h1 := hid ψ hψ.contDiffOn
      have h0 : ∫ x, E x * diffOp A a ψ x = 0 := by
        rw [← integral_zero (EuclideanSpace ℝ (Fin d)) ℂ]
        congr 1
        funext x
        by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) δ
        · rw [hop f g x hx, hQf]; simp
        · rw [image_eq_zero_of_notMem_tsupport fun hE => hx (hρδ (hEs hE)), zero_mul]
      rw [h0, eq_comm, sub_eq_zero] at h1
      have hψ0 : ψ 0 = (f : G → ℂ) g := by simp [ψ]
      rw [← hψ0, h1]
      simp_rw [mul_comm ((f : G → ℂ) _)]
      rw [hκ _ (hfc f g)]

noncomputable def convDeriv (X : 𝔤) (κ : G → ℂ) (y : G) : ℂ :=
  h.rightDeriv X (fun z => κ z⁻¹) y⁻¹

variable {h}

theorem continuous_of_isSmoothFun {f : G → ℂ} (hf : h.IsSmoothFun f) : Continuous f := by
  let _ := h.chartedSpace
  exact ContMDiff.continuous hf

theorem isSmoothFun_comp_inv {κ : G → ℂ}
    (hκ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) :
    h.IsSmoothFun (fun z : G => κ z⁻¹) := by
  let _ := h.chartedSpace
  have := h.lieGroup ∞
  exact hκ.comp (contMDiff_inv 𝓘(ℝ, 𝔤) ∞)

theorem continuous_rightDeriv_comp_inv {κ : G → ℂ}
    (hκ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) (X : 𝔤) :
    Continuous (h.rightDeriv X fun z : G => κ z⁻¹) :=
  continuous_of_isSmoothFun (h.isSmoothFun_rightDeriv (isSmoothFun_comp_inv hκ) X)

theorem continuous_convDeriv {κ : G → ℂ}
    (hκ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) (X : 𝔤) :
    Continuous (h.convDeriv X κ) :=
  (continuous_rightDeriv_comp_inv hκ X).comp continuous_inv

theorem rightDeriv_eq_zero_of_eventually {f : G → ℂ} {g : G} (hf : ∀ᶠ z in 𝓝 g, f z = 0)
    (X : 𝔤) : h.rightDeriv X f g = 0 := by
  have hc : Continuous fun Y : 𝔤 => g * h.expG Y := continuous_const.mul h.continuous_expG
  have h0 : (fun Y : 𝔤 => f (g * h.expG Y)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
    have : Tendsto (fun Y : 𝔤 => g * h.expG Y) (𝓝 0) (𝓝 g) := by
      simpa using hc.tendsto (0 : 𝔤)
    exact this.eventually hf
  simp only [rightDeriv, h0.fderiv_eq, fderiv_const_apply]
  rfl

theorem rightDeriv_comp_inv_eq_zero {κ : G → ℂ} {z : G} (hz : z⁻¹ ∉ tsupport κ) (X : 𝔤) :
    h.rightDeriv X (fun w : G => κ w⁻¹) z = 0 := by
  refine rightDeriv_eq_zero_of_eventually ?_ X
  have hopen : IsOpen (tsupport κ)ᶜ := (isClosed_tsupport κ).isOpen_compl
  have ht : Tendsto (fun w : G => w⁻¹) (𝓝 z) (𝓝 z⁻¹) := continuous_inv.tendsto z
  exact (ht.eventually (hopen.mem_nhds hz)).mono fun w hw =>
    (image_eq_zero_of_notMem_tsupport hw : κ w⁻¹ = 0)

theorem support_convDeriv_subset (X : 𝔤) (κ : G → ℂ) :
    Function.support (h.convDeriv X κ) ⊆ tsupport κ := by
  intro y hy
  by_contra hyκ
  exact hy (rightDeriv_comp_inv_eq_zero (by rwa [inv_inv]) X)

theorem hasCompactSupport_convDeriv {κ : G → ℂ} (hκc : HasCompactSupport κ) (X : 𝔤) :
    HasCompactSupport (h.convDeriv X κ) :=
  hκc.mono' (support_convDeriv_subset X κ)

theorem exists_bound_rightDeriv_comp_inv {κ : G → ℂ}
    (hκ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) (hκc : HasCompactSupport κ)
    (X : 𝔤) : ∃ M, ∀ z, ‖h.rightDeriv X (fun w : G => κ w⁻¹) z‖ ≤ M := by
  have hDcs : HasCompactSupport (h.rightDeriv X fun w : G => κ w⁻¹) := by
    refine HasCompactSupport.intro (hκc.image continuous_inv) fun z hz => ?_
    refine rightDeriv_comp_inv_eq_zero (fun hk => hz ⟨z⁻¹, hk, inv_inv z⟩) X
  exact hDcs.exists_bound_of_continuous (continuous_rightDeriv_comp_inv hκ X)

theorem rightDeriv_eq_integral_convDeriv [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [μ.IsHaarMeasure] {κ : G → ℂ}
    (hκ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) (hκc : HasCompactSupport κ)
    {f : G → ℂ} (hf : h.IsSmoothFun f) (hconv : ∀ g, f g = ∫ y, f (g * y) * κ y ∂μ)
    (X : 𝔤) (g : G) :
    h.rightDeriv X f g = ∫ y, f (g * y) * h.convDeriv X κ y ∂μ := by
  have hec : Continuous fun t : ℝ => h.expG (t • X) :=
    h.continuous_expG.comp (continuous_id.smul continuous_const)
  have hfc : Continuous f := continuous_of_isSmoothFun hf
  have hfg : Continuous fun y : G => f (g * y) := hfc.comp (continuous_const.mul continuous_id)
  have hκ'c : Continuous fun z : G => κ z⁻¹ := continuous_of_isSmoothFun (isSmoothFun_comp_inv hκ)
  have hDc := continuous_rightDeriv_comp_inv hκ X

  have hshift : ∀ t : ℝ, f (g * h.expG (t • X)) =
      ∫ y, f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹ ∂μ := by
    intro t
    rw [hconv (g * h.expG (t • X))]
    have := integral_mul_left_eq_self (μ := μ)
      (fun y => f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹) (h.expG (t • X))
    rw [← this]
    congr 1
    funext y
    simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, inv_inv]

  have hderiv : ∀ (y : G) (t : ℝ), HasDerivAt (fun s : ℝ => κ (y⁻¹ * h.expG (s • X))⁻¹)
      (h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X))) t := by
    intro y t
    have h1 := h.hasDerivAt_rightDeriv (isSmoothFun_comp_inv hκ) X (y⁻¹ * h.expG (t • X))
    have h1' : HasDerivAt (fun s : ℝ => κ (y⁻¹ * h.expG (t • X) * h.expG (s • X))⁻¹)
        (h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X))) (t - t) := by
      rw [sub_self]; exact h1
    refine (h1'.comp_sub_const t t).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp only [mul_assoc, ← h.expG_add_smul, add_sub_cancel]

  set S : Set G := (fun p : ℝ × G => h.expG (p.1 • X) * p.2) ''
    (Metric.closedBall (0 : ℝ) 1 ×ˢ tsupport κ) with hSdef
  have hS : IsCompact S :=
    ((isCompact_closedBall 0 1).prod hκc).image
      ((hec.comp continuous_fst).mul continuous_snd)
  have hvanish : ∀ (y : G) (t : ℝ), t ∈ Metric.closedBall (0 : ℝ) 1 → y ∉ S →
      h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X)) = 0 := by
    intro y t ht hy
    refine rightDeriv_comp_inv_eq_zero (fun hk => hy ⟨(t, (h.expG (t • X))⁻¹ * y), ⟨ht, ?_⟩, ?_⟩) X
    · simpa [mul_inv_rev] using hk
    · simp
  obtain ⟨M, hM⟩ := exists_bound_rightDeriv_comp_inv hκ hκc X
  have hbound : Integrable (S.indicator fun y => ‖f (g * y)‖ * M) μ := by
    refine IntegrableOn.integrable_indicator ?_ hS.measurableSet
    exact (hfg.norm.mul continuous_const).continuousOn.integrableOn_compact hS
  have hint0 : Integrable (fun y => f (g * y) * κ (y⁻¹ * h.expG ((0 : ℝ) • X))⁻¹) μ := by
    have : (fun y => f (g * y) * κ (y⁻¹ * h.expG ((0 : ℝ) • X))⁻¹) = fun y => f (g * y) * κ y := by
      funext y; simp
    rw [this]
    exact Continuous.integrable_of_hasCompactSupport (hfg.mul (continuous_of_isSmoothFun (f := κ) hκ))
      (hκc.mono' fun y hy => subset_tsupport κ (right_ne_zero_of_mul hy))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun (t : ℝ) (y : G) => f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹)
    (F' := fun (t : ℝ) (y : G) => f (g * y) *
      h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X)))
    (x₀ := (0 : ℝ)) (s := Metric.ball (0 : ℝ) 1)
    (bound := S.indicator fun y => ‖f (g * y)‖ * M)
    (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun t =>
      (hfg.mul (hκ'c.comp (continuous_inv.mul continuous_const))).aestronglyMeasurable) hint0
    (hfg.mul (hDc.comp (continuous_inv.mul continuous_const))).aestronglyMeasurable
    (Eventually.of_forall fun y t ht => by
      by_cases hy : y ∈ S
      · rw [indicator_of_mem hy, norm_mul]
        exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
      · rw [indicator_of_notMem hy, hvanish y t (Metric.ball_subset_closedBall ht) hy, mul_zero,
          norm_zero])
    hbound
    (Eventually.of_forall fun y t _ => (hderiv y t).const_mul (f (g * y)))
  have hd1 : HasDerivAt (fun t : ℝ => f (g * h.expG (t • X))) (h.rightDeriv X f g) 0 :=
    h.hasDerivAt_rightDeriv hf X g
  have hd2 := key.2.congr_of_eventuallyEq (Eventually.of_forall hshift)
  rw [hd1.unique hd2]
  congr 1
  funext y
  simp [convDeriv]

end IsExpLieAlgebra

end GroundTheory.Automorphic
