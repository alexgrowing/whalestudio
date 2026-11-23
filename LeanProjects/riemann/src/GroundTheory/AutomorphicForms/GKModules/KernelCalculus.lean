import Mathlib
import GroundTheory.AutomorphicForms.GKModules.Garding
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableConv

namespace GroundTheory.Automorphic

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff Manifold

set_option linter.unusedSectionVars false

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

variable {h} in

theorem IsTestFunction.convDeriv {γ : G → ℂ} (hγ : h.IsTestFunction γ) (X : 𝔤) :
    h.IsTestFunction (h.convDeriv X γ) := by
  refine ⟨?_, hasCompactSupport_convDeriv hγ.2 X⟩
  let _ := h.chartedSpace
  have := h.lieGroup ∞
  have h1 : h.IsSmoothFun (h.rightDeriv X fun z : G => γ z⁻¹) :=
    h.isSmoothFun_rightDeriv (isSmoothFun_comp_inv hγ.1) X
  exact ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) h1 (contMDiff_inv 𝓘(ℝ, 𝔤) ∞)

variable {h} in

theorem IsTestFunction.const_mul {γ : G → ℂ} (hγ : h.IsTestFunction γ) (c : ℂ) :
    h.IsTestFunction (fun y => c * γ y) := by
  refine ⟨?_, hγ.2.mul_left⟩
  let _ := h.chartedSpace
  set L : ℂ →L[ℝ] ℂ := (c • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ
  have e : (fun y => c * γ y) = L ∘ γ := by funext y; simp [L]
  rw [e]
  exact L.contDiff.comp_contMDiff hγ.1

variable {h} in

theorem IsTestFunction.add {γ₁ γ₂ : G → ℂ} (h₁ : h.IsTestFunction γ₁) (h₂ : h.IsTestFunction γ₂) :
    h.IsTestFunction (fun y => γ₁ y + γ₂ y) := by
  refine ⟨?_, h₁.2.add h₂.2⟩
  let _ := h.chartedSpace
  exact h₁.1.add h₂.1

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

theorem integral_mul_left_kernel (Ψ γ : G → ℂ) (a : G) :
    ∫ y, Ψ (a * y) * γ y ∂μ = ∫ y, Ψ y * γ (a⁻¹ * y) ∂μ := by
  calc ∫ y, Ψ (a * y) * γ y ∂μ = ∫ y, (fun y => Ψ y * γ (a⁻¹ * y)) (a * y) ∂μ := by
        congr 1; funext y; simp
    _ = ∫ y, Ψ y * γ (a⁻¹ * y) ∂μ := integral_mul_left_eq_self (μ := μ) (fun y => Ψ y * γ (a⁻¹ * y)) a

theorem integrable_mul_test {Ψ : G → ℂ} (hΨ : Continuous Ψ) {γ : G → ℂ}
    (hγ : h.IsTestFunction γ) (g : G) : Integrable (fun y => Ψ (g * y) * γ y) μ :=
  ((hΨ.comp (continuous_const.mul continuous_id)).mul (hγ.continuous h)).integrable_of_hasCompactSupport
    hγ.2.mul_left

theorem isSmoothFun_integral_mul {Ψ : G → ℂ} (hΨ : Continuous Ψ) {γ : G → ℂ}
    (hγ : h.IsTestFunction γ) : h.IsSmoothFun (fun g => ∫ y, Ψ (g * y) * γ y ∂μ) := by
  have := secondCountableTopology_subgroup_units G
  rw [isSmoothFun_iff]
  intro g₀
  set F : 𝔤 → G → ℂ := fun Y y => γ (h.expG (-Y) * (g₀⁻¹ * y)) * Ψ y with hFdef
  have hexp : (fun Y : 𝔤 => ∫ y, Ψ (g₀ * h.expG Y * y) * γ y ∂μ) = fun Y => ∫ y, F Y y ∂μ := by
    funext Y
    rw [integral_mul_left_kernel]
    congr 1; funext y
    simp only [hFdef, h.expG_neg, mul_inv_rev, mul_assoc]
    ring
  show ContDiff ℝ ∞ (fun Y : 𝔤 => ∫ y, Ψ (g₀ * h.expG Y * y) * γ y ∂μ)
  rw [hexp]
  set ψ : 𝔤 → G → ℂ := fun Y y => γ (h.expG (-Y) * (g₀⁻¹ * y)) with hψdef
  have hψ : ∀ g₁ : G, ContDiff ℝ ∞ (fun q : 𝔤 × 𝔤 => ψ q.1 (g₁ * h.expG q.2)) := by
    intro g₁
    have := h.contDiff_comp_expG_mul_expG hγ.1 (contDiff_fst.neg) (g₀⁻¹ * g₁) contDiff_snd
    simpa [hψdef, mul_assoc] using this
  have hψY : ∀ y : G, ContDiff ℝ ∞ (fun Y => ψ Y y) := by
    intro y
    have := h.contDiff_comp_expG_mul_expG hγ.1 (contDiff_id.neg) (g₀⁻¹ * y)
      (contDiff_const (c := (0 : 𝔤)))
    simpa [hψdef] using this
  set Lw : G → ℂ →L[ℝ] ℂ := fun y => (ContinuousLinearMap.lsmul ℝ ℂ).flip (Ψ y) with hLw
  have hLwc : Continuous Lw := (ContinuousLinearMap.continuous _).comp hΨ
  have hFL : ∀ y, (fun Y => F Y y) = Lw y ∘ fun Y => ψ Y y := by
    intro y; funext Y; simp [hFdef, hLw, hψdef]
  have hiter : ∀ (k : ℕ) (Y : 𝔤) (y : G), ParamIntegral.iter F k Y y =
      (Lw y).compContinuousMultilinearMap (iteratedFDeriv ℝ k (fun Y => ψ Y y) Y) := by
    intro k Y y
    rw [ParamIntegral.iter, hFL y]
    exact (Lw y).iteratedFDeriv_comp_left (hψY y).contDiffAt (by exact_mod_cast le_top)
  refine contDiff_integral_of_iteratedFDeriv F (fun y => ?_) (fun k => ?_) (fun Y₀ => ?_)
  · rw [hFL y]; exact (Lw y).contDiff.comp (hψY y)
  · simp_rw [hiter]
    have hc := h.continuous_iteratedFDeriv_param ψ hψ k
    have hB := ContinuousLinearMap.continuous₂ (𝕜 := ℝ) (E := ℂ →L[ℝ] ℂ)
      (F := ContinuousMultilinearMap ℝ (fun _ : Fin k => 𝔤) ℂ)
      (G := ContinuousMultilinearMap ℝ (fun _ : Fin k => 𝔤) ℂ)
      (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k => 𝔤) ℂ ℂ)
    exact hB.comp ((hLwc.comp continuous_snd).prodMk hc)
  · refine ⟨closedBall Y₀ 1, closedBall_mem_nhds Y₀ one_pos,
      (fun p : 𝔤 × G => g₀ * (h.expG p.1 * p.2)) '' (closedBall Y₀ 1 ×ˢ tsupport γ), ?_, ?_⟩
    · exact ((isCompact_closedBall Y₀ 1).prod hγ.2).image
        (continuous_const.mul ((h.continuous_expG.comp continuous_fst).mul continuous_snd))
    · intro Y hY y hy
      simp only [hFdef]
      by_contra hne
      apply hy
      refine ⟨(Y, h.expG (-Y) * (g₀⁻¹ * y)), ⟨hY, subset_tsupport γ ?_⟩, ?_⟩
      · intro h0; apply hne; simp [h0]
      · simp [h.expG_neg]

theorem rightDeriv_integral_mul {Ψ : G → ℂ} (hΨ : Continuous Ψ) {γ : G → ℂ}
    (hγ : h.IsTestFunction γ) (X : 𝔤) (g : G) :
    h.rightDeriv X (fun g => ∫ y, Ψ (g * y) * γ y ∂μ) g = ∫ y, Ψ (g * y) * h.convDeriv X γ y ∂μ := by
  have hec : Continuous fun t : ℝ => h.expG (t • X) :=
    h.continuous_expG.comp (continuous_id.smul continuous_const)
  have hfg : Continuous fun y : G => Ψ (g * y) := hΨ.comp (continuous_const.mul continuous_id)
  have hκ'c : Continuous fun z : G => γ z⁻¹ := continuous_of_isSmoothFun (isSmoothFun_comp_inv hγ.1)
  have hDc := continuous_rightDeriv_comp_inv hγ.1 X

  have hshift : ∀ t : ℝ, (fun g => ∫ y, Ψ (g * y) * γ y ∂μ) (g * h.expG (t • X)) =
      ∫ y, Ψ (g * y) * γ (y⁻¹ * h.expG (t • X))⁻¹ ∂μ := by
    intro t
    show ∫ y, Ψ (g * h.expG (t • X) * y) * γ y ∂μ = _
    have := integral_mul_left_eq_self (μ := μ)
      (fun y => Ψ (g * y) * γ (y⁻¹ * h.expG (t • X))⁻¹) (h.expG (t • X))
    rw [← this]
    congr 1
    funext y
    simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, inv_inv]

  have hderiv : ∀ (y : G) (t : ℝ), HasDerivAt (fun s : ℝ => γ (y⁻¹ * h.expG (s • X))⁻¹)
      (h.rightDeriv X (fun w : G => γ w⁻¹) (y⁻¹ * h.expG (t • X))) t := by
    intro y t
    have h1 := h.hasDerivAt_rightDeriv (isSmoothFun_comp_inv hγ.1) X (y⁻¹ * h.expG (t • X))
    have h1' : HasDerivAt (fun s : ℝ => γ (y⁻¹ * h.expG (t • X) * h.expG (s • X))⁻¹)
        (h.rightDeriv X (fun w : G => γ w⁻¹) (y⁻¹ * h.expG (t • X))) (t - t) := by
      rw [sub_self]; exact h1
    refine (h1'.comp_sub_const t t).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp only [mul_assoc, ← h.expG_add_smul, add_sub_cancel]

  set S : Set G := (fun p : ℝ × G => h.expG (p.1 • X) * p.2) ''
    (Metric.closedBall (0 : ℝ) 1 ×ˢ tsupport γ) with hSdef
  have hS : IsCompact S :=
    ((isCompact_closedBall 0 1).prod hγ.2).image
      ((hec.comp continuous_fst).mul continuous_snd)
  have hvanish : ∀ (y : G) (t : ℝ), t ∈ Metric.closedBall (0 : ℝ) 1 → y ∉ S →
      h.rightDeriv X (fun w : G => γ w⁻¹) (y⁻¹ * h.expG (t • X)) = 0 := by
    intro y t ht hy
    refine rightDeriv_comp_inv_eq_zero (fun hk => hy ⟨(t, (h.expG (t • X))⁻¹ * y), ⟨ht, ?_⟩, ?_⟩) X
    · simpa [mul_inv_rev] using hk
    · simp
  obtain ⟨M, hM⟩ := exists_bound_rightDeriv_comp_inv hγ.1 hγ.2 X
  have hbound : Integrable (S.indicator fun y => ‖Ψ (g * y)‖ * M) μ := by
    refine IntegrableOn.integrable_indicator ?_ hS.measurableSet
    exact (hfg.norm.mul continuous_const).continuousOn.integrableOn_compact hS
  have hint0 : Integrable (fun y => Ψ (g * y) * γ (y⁻¹ * h.expG ((0 : ℝ) • X))⁻¹) μ := by
    have : (fun y => Ψ (g * y) * γ (y⁻¹ * h.expG ((0 : ℝ) • X))⁻¹) = fun y => Ψ (g * y) * γ y := by
      funext y; simp
    rw [this]
    exact h.integrable_mul_test μ hΨ hγ g
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun (t : ℝ) (y : G) => Ψ (g * y) * γ (y⁻¹ * h.expG (t • X))⁻¹)
    (F' := fun (t : ℝ) (y : G) => Ψ (g * y) *
      h.rightDeriv X (fun w : G => γ w⁻¹) (y⁻¹ * h.expG (t • X)))
    (x₀ := (0 : ℝ)) (s := Metric.ball (0 : ℝ) 1)
    (bound := S.indicator fun y => ‖Ψ (g * y)‖ * M)
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
    (Eventually.of_forall fun y t _ => (hderiv y t).const_mul (Ψ (g * y)))
  have hd1 := h.hasDerivAt_rightDeriv (h.isSmoothFun_integral_mul μ hΨ hγ) X g
  have hd2 := key.2.congr_of_eventuallyEq (Eventually.of_forall hshift)
  rw [hd1.unique hd2]
  congr 1
  funext y
  simp [convDeriv]

theorem integral_mul_add {Ψ : G → ℂ} (hΨ : Continuous Ψ) {γ₁ γ₂ : G → ℂ}
    (h₁ : h.IsTestFunction γ₁) (h₂ : h.IsTestFunction γ₂) (g : G) :
    ∫ y, Ψ (g * y) * (γ₁ y + γ₂ y) ∂μ = ∫ y, Ψ (g * y) * γ₁ y ∂μ + ∫ y, Ψ (g * y) * γ₂ y ∂μ := by
  simp_rw [mul_add]
  exact integral_add (h.integrable_mul_test μ hΨ h₁ g) (h.integrable_mul_test μ hΨ h₂ g)

theorem integral_mul_const_mul (Ψ γ : G → ℂ) (c : ℂ) (g : G) :
    ∫ y, Ψ (g * y) * (c * γ y) ∂μ = c * ∫ y, Ψ (g * y) * γ y ∂μ := by
  rw [← integral_const_mul]
  congr 1; funext y; ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (π : BanachRep G E)

theorem integrated_add_kernel {γ₁ γ₂ : G → ℂ} (h₁ : h.IsTestFunction γ₁) (h₂ : h.IsTestFunction γ₂)
    (w : E) : π.integrated μ (fun y => γ₁ y + γ₂ y) w = π.integrated μ γ₁ w + π.integrated μ γ₂ w := by
  unfold BanachRep.integrated
  simp_rw [add_smul]
  exact integral_add (h.integrable_smul_orbit π μ h₁ w) (h.integrable_smul_orbit π μ h₂ w)

theorem integrated_const_mul_kernel (γ : G → ℂ) (c : ℂ) (w : E) :
    π.integrated μ (fun y => c * γ y) w = c • π.integrated μ γ w := by
  unfold BanachRep.integrated
  rw [← integral_smul]
  congr 1; funext y; rw [mul_smul]

theorem derivOp_integrated_convDeriv {γ : G → ℂ} (hγ : h.IsTestFunction γ) (w : E) (X : 𝔤) :
    h.derivOp π X (π.integrated μ γ w) = π.integrated μ (h.convDeriv X γ) w := by
  have := secondCountableTopology_subgroup_units G
  have hec : Continuous fun t : ℝ => h.expG (t • X) :=
    h.continuous_expG.comp (continuous_id.smul continuous_const)
  have hw : Continuous fun y : G => π y w := π.continuous_orbit w
  have hκ'c : Continuous fun z : G => γ z⁻¹ := continuous_of_isSmoothFun (isSmoothFun_comp_inv hγ.1)
  have hDc := continuous_rightDeriv_comp_inv hγ.1 X

  have hshift : ∀ t : ℝ, π (h.expG (t • X)) (π.integrated μ γ w) =
      ∫ y, γ (y⁻¹ * h.expG (t • X))⁻¹ • π y w ∂μ := by
    intro t
    rw [BanachRep.integrated,
      ← (π (h.expG (t • X))).integral_comp_comm (h.integrable_smul_orbit π μ hγ w)]
    have := integral_mul_left_eq_self (μ := μ)
      (fun y => γ (y⁻¹ * h.expG (t • X))⁻¹ • π y w) (h.expG (t • X))
    rw [← this]
    congr 1
    funext y
    simp only [map_smul, ← BanachRep.map_mul_apply, mul_inv_rev, mul_assoc, inv_mul_cancel_left,
      inv_inv]
  have hderiv : ∀ (y : G) (t : ℝ), HasDerivAt (fun s : ℝ => γ (y⁻¹ * h.expG (s • X))⁻¹)
      (h.rightDeriv X (fun w : G => γ w⁻¹) (y⁻¹ * h.expG (t • X))) t := by
    intro y t
    have h1 := h.hasDerivAt_rightDeriv (isSmoothFun_comp_inv hγ.1) X (y⁻¹ * h.expG (t • X))
    have h1' : HasDerivAt (fun s : ℝ => γ (y⁻¹ * h.expG (t • X) * h.expG (s • X))⁻¹)
        (h.rightDeriv X (fun w : G => γ w⁻¹) (y⁻¹ * h.expG (t • X))) (t - t) := by
      rw [sub_self]; exact h1
    refine (h1'.comp_sub_const t t).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp only [mul_assoc, ← h.expG_add_smul, add_sub_cancel]
  set S : Set G := (fun p : ℝ × G => h.expG (p.1 • X) * p.2) ''
    (Metric.closedBall (0 : ℝ) 1 ×ˢ tsupport γ) with hSdef
  have hS : IsCompact S :=
    ((isCompact_closedBall 0 1).prod hγ.2).image
      ((hec.comp continuous_fst).mul continuous_snd)
  have hvanish : ∀ (y : G) (t : ℝ), t ∈ Metric.closedBall (0 : ℝ) 1 → y ∉ S →
      h.rightDeriv X (fun w : G => γ w⁻¹) (y⁻¹ * h.expG (t • X)) = 0 := by
    intro y t ht hy
    refine rightDeriv_comp_inv_eq_zero (fun hk => hy ⟨(t, (h.expG (t • X))⁻¹ * y), ⟨ht, ?_⟩, ?_⟩) X
    · simpa [mul_inv_rev] using hk
    · simp
  obtain ⟨M, hM⟩ := exists_bound_rightDeriv_comp_inv hγ.1 hγ.2 X
  have hbound : Integrable (S.indicator fun y => M * ‖π y w‖) μ := by
    refine IntegrableOn.integrable_indicator ?_ hS.measurableSet
    exact (continuous_const.mul hw.norm).continuousOn.integrableOn_compact hS
  have hint0 : Integrable (fun y => γ (y⁻¹ * h.expG ((0 : ℝ) • X))⁻¹ • π y w) μ := by
    have : (fun y => γ (y⁻¹ * h.expG ((0 : ℝ) • X))⁻¹ • π y w) = fun y => γ y • π y w := by
      funext y; simp
    rw [this]
    exact h.integrable_smul_orbit π μ hγ w
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun (t : ℝ) (y : G) => γ (y⁻¹ * h.expG (t • X))⁻¹ • π y w)
    (F' := fun (t : ℝ) (y : G) =>
      h.rightDeriv X (fun w : G => γ w⁻¹) (y⁻¹ * h.expG (t • X)) • π y w)
    (x₀ := (0 : ℝ)) (s := Metric.ball (0 : ℝ) 1)
    (bound := S.indicator fun y => M * ‖π y w‖)
    (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun t =>
      ((hκ'c.comp (continuous_inv.mul continuous_const)).smul hw).aestronglyMeasurable) hint0
    ((hDc.comp (continuous_inv.mul continuous_const)).smul hw).aestronglyMeasurable
    (Eventually.of_forall fun y t ht => by
      by_cases hy : y ∈ S
      · rw [indicator_of_mem hy, norm_smul]
        exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
      · rw [indicator_of_notMem hy, hvanish y t (Metric.ball_subset_closedBall ht) hy, zero_smul,
          norm_zero])
    hbound
    (Eventually.of_forall fun y t _ => (hderiv y t).smul_const (π y w))
  have hd1 := h.hasDerivAt_derivOp π (h.isSmoothVector_integrated π μ hγ w) X
  have hd2 := key.2.congr_of_eventuallyEq (Eventually.of_forall hshift)
  rw [hd1.unique hd2]
  unfold BanachRep.integrated
  congr 1
  funext y
  simp [convDeriv]

theorem exists_uAction_integrated (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) {γ : G → ℂ}
    (hγ : h.IsTestFunction γ) :
    ∃ γ', h.IsTestFunction γ' ∧
      (∀ w : E, (h.uAction π u ⟨π.integrated μ γ w, h.isSmoothVector_integrated π μ hγ w⟩ : E) =
        π.integrated μ γ' w) ∧
      ∀ (Ψ : G → ℂ) (hΨ : Continuous Ψ),
        (h.rightUAction (F := ℂ) u
            ⟨fun g => ∫ y, Ψ (g * y) * γ y ∂μ, h.isSmoothFun_integral_mul μ hΨ hγ⟩ : G → ℂ) =
          fun g => ∫ y, Ψ (g * y) * γ' y ∂μ := by
  obtain ⟨t, rfl⟩ : ∃ t, UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra t = u :=
    RingCon.mkₐ_surjective (α := ℝ) (UniversalEnvelopingAlgebra.ringCon ℝ h.lieSubalgebra) u
  induction t using TensorAlgebra.induction generalizing γ with
  | algebraMap r =>
    refine ⟨fun y => (r : ℂ) * γ y, hγ.const_mul _, fun w => ?_, fun Ψ hΨ => ?_⟩
    · rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply, integrated_const_mul_kernel]
      show r • π.integrated μ γ w = (r : ℂ) • π.integrated μ γ w
      exact (Complex.coe_smul r _).symm
    · rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply]
      funext g
      show r • (∫ y, Ψ (g * y) * γ y ∂μ) = ∫ y, Ψ (g * y) * ((r : ℂ) * γ y) ∂μ
      rw [integral_mul_const_mul, Complex.real_smul]
  | ι x =>
    refine ⟨h.convDeriv (h.ofLie x) γ, hγ.convDeriv _, fun w => ?_, fun Ψ hΨ => ?_⟩
    · show (h.uAction π (UniversalEnvelopingAlgebra.ι ℝ x)
        ⟨π.integrated μ γ w, h.isSmoothVector_integrated π μ hγ w⟩ : E) = _
      rw [uAction_ι, coe_derivEnd, h.derivOp_integrated_convDeriv μ π hγ]
    · show (h.rightUAction (F := ℂ) (UniversalEnvelopingAlgebra.ι ℝ x)
        ⟨fun g => ∫ y, Ψ (g * y) * γ y ∂μ, h.isSmoothFun_integral_mul μ hΨ hγ⟩ : G → ℂ) = _
      rw [rightUAction_ι, coe_rightDerivEnd]
      funext g
      exact h.rightDeriv_integral_mul μ hΨ hγ _ g
  | mul a b ha hb =>
    obtain ⟨γb, hγb, hb1, hb2⟩ := hb hγ
    obtain ⟨γab, hγab, ha1, ha2⟩ := ha hγb
    refine ⟨γab, hγab, fun w => ?_, fun Ψ hΨ => ?_⟩
    · rw [map_mul, map_mul, Module.End.mul_apply]
      have e : h.uAction π (UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra b)
          ⟨π.integrated μ γ w, h.isSmoothVector_integrated π μ hγ w⟩ =
          ⟨π.integrated μ γb w, h.isSmoothVector_integrated π μ hγb w⟩ := Subtype.ext (hb1 w)
      rw [e]
      exact ha1 w
    · rw [map_mul, map_mul, Module.End.mul_apply]
      have e : h.rightUAction (F := ℂ) (UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra b)
          ⟨fun g => ∫ y, Ψ (g * y) * γ y ∂μ, h.isSmoothFun_integral_mul μ hΨ hγ⟩ =
          ⟨fun g => ∫ y, Ψ (g * y) * γb y ∂μ, h.isSmoothFun_integral_mul μ hΨ hγb⟩ :=
        Subtype.ext (hb2 Ψ hΨ)
      rw [e]
      exact ha2 Ψ hΨ
  | add a b ha hb =>
    obtain ⟨γa, hγa, ha1, ha2⟩ := ha hγ
    obtain ⟨γb, hγb, hb1, hb2⟩ := hb hγ
    refine ⟨fun y => γa y + γb y, hγa.add hγb, fun w => ?_, fun Ψ hΨ => ?_⟩
    · rw [map_add, map_add, LinearMap.add_apply, Submodule.coe_add, ha1 w, hb1 w,
        integrated_add_kernel h μ π hγa hγb]
    · rw [map_add, map_add, LinearMap.add_apply, Submodule.coe_add, ha2 Ψ hΨ, hb2 Ψ hΨ]
      funext g
      exact (h.integral_mul_add μ hΨ hγa hγb g).symm

end IsExpLieAlgebra

end GroundTheory.Automorphic
