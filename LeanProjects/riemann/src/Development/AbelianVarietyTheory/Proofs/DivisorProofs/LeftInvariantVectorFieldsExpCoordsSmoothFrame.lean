import Development.AbelianVarietyTheory.Definitions.Divisors.ZeroMemSolSet
import Formalism.UnipotentAdelicQuotients.EllRegCheck
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.ExpCoordFrame

open NormedSpace Filter Topology

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} {d : ℕ}

local notation "𝔢" => expPartialHomeomorph ℝ 𝔸

noncomputable def psi (b : Module.Basis (Fin d) ℝ 𝔤) (x : E d) (Y : 𝔤) : E d :=
  (coordEquiv b).symm (subspaceProj 𝔤 ((𝔢).symm (exp ((coordEquiv b x : 𝔤) : 𝔸) * exp (Y : 𝔸))))

theorem contDiffAt_psi (b : Module.Basis (Fin d) ℝ 𝔤) (x : E d)
    (hx : ((coordEquiv b x : 𝔤) : 𝔸) ∈ (𝔢).source) :
    ContDiffAt ℝ ∞ (Function.uncurry (psi b)) (x, 0) := by
  have hin : exp ((coordEquiv b x : 𝔤) : 𝔸) * exp (((0 : 𝔤)) : 𝔸) ∈ (𝔢).target := by
    have e : exp ((coordEquiv b x : 𝔤) : 𝔸) ∈ (𝔢).target := (𝔢).map_source hx
    simpa using e
  have hlog : ContDiffAt ℝ ∞ (𝔢).symm (exp ((coordEquiv b x : 𝔤) : 𝔸) * exp (((0 : 𝔤)) : 𝔸)) :=
    (contDiffOn_expPartialHomeomorph_symm ℝ 𝔸).contDiffAt ((𝔢).open_target.mem_nhds hin)
  have hm : ContDiff ℝ ∞ (fun p : E d × 𝔤 => exp ((coordEquiv b p.1 : 𝔤) : 𝔸) * exp (p.2 : 𝔸)) :=
    ((contDiff_exp ℝ 𝔸).comp (𝔤.subtypeL.contDiff.comp ((coordEquiv b).contDiff.comp contDiff_fst))).mul
      ((contDiff_exp ℝ 𝔸).comp (𝔤.subtypeL.contDiff.comp contDiff_snd))
  exact (coordEquiv b).symm.contDiff.comp_contDiffAt (x, (0 : 𝔤))
    ((subspaceProj 𝔤).contDiff.comp_contDiffAt (x, (0 : 𝔤)) (hlog.comp (x, (0 : 𝔤)) hm.contDiffAt))

theorem psi_zero (b : Module.Basis (Fin d) ℝ 𝔤) (x : E d)
    (hx : ((coordEquiv b x : 𝔤) : 𝔸) ∈ (𝔢).source) : psi b x 0 = x := by
  simp only [psi, ZeroMemClass.coe_zero, exp_zero, mul_one]
  have e : (𝔢).symm (exp ((coordEquiv b x : 𝔤) : 𝔸)) = ((coordEquiv b x : 𝔤) : 𝔸) := (𝔢).left_inv hx
  rw [e, subspaceProj_coe, ContinuousLinearEquiv.symm_apply_apply]

theorem psi_origin_eventually (b : Module.Basis (Fin d) ℝ 𝔤) :
    psi b 0 =ᶠ[𝓝 (0 : 𝔤)] (coordEquiv b).symm := by
  have hs : {Y : 𝔤 | (Y : 𝔸) ∈ (𝔢).source} ∈ 𝓝 (0 : 𝔤) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds
      ((𝔢).open_source.mem_nhds (zero_mem_expPartialHomeomorph_source ℝ 𝔸))
  filter_upwards [hs] with Y hY
  simp only [psi, coordEquiv_zero, ZeroMemClass.coe_zero, exp_zero, one_mul]
  have e : (𝔢).symm (exp (Y : 𝔸)) = (Y : 𝔸) := (𝔢).left_inv hY
  rw [e, subspaceProj_coe]

theorem expG_psi (h : IsExpLieAlgebra G 𝔤) (b : Module.Basis (Fin d) ℝ 𝔤) (x : E d)
    (hx : ((coordEquiv b x : 𝔤) : 𝔸) ∈ h.nhd) :
    ∀ᶠ Y in 𝓝 (0 : 𝔤), h.expG (coordEquiv b (psi b x Y)) = h.expG (coordEquiv b x) * h.expG Y := by
  have hc : Continuous (fun Y : 𝔤 => exp ((coordEquiv b x : 𝔤) : 𝔸) * exp (Y : 𝔸)) :=
    continuous_const.mul ((contDiff_exp ℝ 𝔸 (n := 0)).continuous.comp continuous_subtype_val)
  have h0 : exp ((coordEquiv b x : 𝔤) : 𝔸) * exp (((0 : 𝔤)) : 𝔸) ∈ h.nhdOne := by
    simpa using h.exp_mem_nhdOne hx
  filter_upwards [hc.continuousAt.preimage_mem_nhds (h.isOpen_nhdOne.mem_nhds h0)] with Y hY
  have hY' : exp ((coordEquiv b x : 𝔤) : 𝔸) * exp (Y : 𝔸) ∈ h.nhdOne := hY
  have hv : (((h.expG (coordEquiv b x) * h.expG Y : G) : 𝔸ˣ) : 𝔸) =
      exp ((coordEquiv b x : 𝔤) : 𝔸) * exp (Y : 𝔸) := by simp
  have hmem := h.symm_mem_lie (x := h.expG (coordEquiv b x) * h.expG Y) (by rw [hv]; exact hY')
  rw [hv] at hmem
  apply Subtype.ext; apply Units.ext
  rw [hv]
  simp only [psi, ContinuousLinearEquiv.apply_symm_apply, IsExpLieAlgebra.coe_expG]
  rw [subspaceProj_of_mem hmem, h.exp_symm hY']

end GlobalTheory.ExpCoordFrame

namespace GlobalTheory.ExpCoordFrame

open NormedSpace Filter Topology

theorem differentiableAt_psi {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] {𝔤 : Submodule ℝ 𝔸} {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (x : E d)
    (hx : ((coordEquiv b x : 𝔤) : 𝔸) ∈ (expPartialHomeomorph ℝ 𝔸).source) :
    DifferentiableAt ℝ (psi b x) 0 := by
  have := (contDiffAt_psi b x hx).comp (0 : 𝔤) ((contDiffAt_const (c := x)).prodMk contDiffAt_id)
  exact this.differentiableAt (by simp)

theorem leftInvariant_frame (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤)
    (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ r > 0, ∃ c : 𝔤 → Fin d → E d → ℝ, (∀ X j, ContDiffOn ℝ ∞ (c X j) (Metric.ball 0 r)) ∧
      (∀ x ∈ Metric.ball (0 : E d) r, ∀ ξ : E d, ξ ≠ 0 → ∃ i, ∑ j, c (b i) j x * ξ j ≠ 0) ∧
      ∀ f : G → ℂ, h.IsSmoothFun f → ∀ X : 𝔤, ∀ x ∈ Metric.ball (0 : E d) r,
        h.rightDeriv X f (h.expG (coordEquiv b (x))) =
          ∑ j, (c X j x : ℂ) * fderiv ℝ (fun y => f (h.expG (coordEquiv b (y)))) x (ev j) := by
  obtain ⟨r₁, hr₁, hball₁⟩ : ∃ r₁ > 0,
      Metric.ball (0 : E d) r₁ ⊆ {x | ((coordEquiv b x : 𝔤) : 𝔸) ∈ h.nhd} := by
    have ho : IsOpen {x : E d | ((coordEquiv b x : 𝔤) : 𝔸) ∈ h.nhd} :=
      h.isOpen_nhd.preimage (continuous_subtype_val.comp (coordEquiv b).continuous)
    exact Metric.isOpen_iff.1 ho 0 (by simpa [coordEquiv_zero] using h.zero_mem_nhd)
  set A : E d → 𝔤 →L[ℝ] E d := fun x => fderiv ℝ (psi b x) 0 with hA
  have hAx : ∀ x ∈ Metric.ball (0 : E d) r₁, ContDiffAt ℝ ∞ A x := fun x hx =>
    (contDiffAt_psi b x (h.nhd_subset (hball₁ hx))).fderiv (contDiffAt_const (c := (0 : 𝔤)))
      (by simp)
  set B : E d → E d →L[ℝ] E d := fun x => (A x).comp (coordEquiv b : E d →L[ℝ] 𝔤) with hB
  have hA0 : A 0 = ((coordEquiv b).symm : 𝔤 →L[ℝ] E d) := by
    simp only [hA]
    rw [(psi_origin_eventually b).fderiv_eq, ContinuousLinearEquiv.fderiv]
  have hB0 : IsUnit (B 0) := by
    have : B 0 = 1 := by
      ext v; simp [hB, hA0]
    rw [this]; exact isUnit_one
  have hBc : ContinuousAt B 0 :=
    ((hAx 0 (Metric.mem_ball_self hr₁)).clm_comp contDiffAt_const).continuousAt
  have hU : {x | IsUnit (B x)} ∈ 𝓝 (0 : E d) := hBc.preimage_mem_nhds (Units.isOpen.mem_nhds hB0)
  obtain ⟨r₂, hr₂, hball₂⟩ := Metric.mem_nhds_iff.1 hU
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun X j x => A x X j, ?_, ?_, ?_⟩
  · intro X j x hx
    have hx1 : x ∈ Metric.ball (0 : E d) r₁ := Metric.ball_subset_ball (min_le_left _ _) hx
    exact ((EuclideanSpace.proj j : E d →L[ℝ] ℝ).contDiff.comp_contDiffAt x
      ((hAx x hx1).clm_apply contDiffAt_const)).contDiffWithinAt
  · intro x hx ξ hξ
    by_contra hcon
    push_neg at hcon
    have hx2 : x ∈ Metric.ball (0 : E d) r₂ := Metric.ball_subset_ball (min_le_right _ _) hx
    obtain ⟨u, hu⟩ : IsUnit (B x) := hball₂ hx2
    set ℓ : 𝔤 →L[ℝ] ℝ := ∑ j, ξ j • ((EuclideanSpace.proj j : E d →L[ℝ] ℝ).comp (A x)) with hℓ
    have hℓ0 : (ℓ : 𝔤 →ₗ[ℝ] ℝ) = 0 := b.ext fun i => by
      have := hcon i
      simp only [hℓ, ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_coe,
        Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
        ContinuousLinearMap.coe_comp', Function.comp_apply, smul_eq_mul, LinearMap.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]; rfl
    set X : 𝔤 := coordEquiv b (((u⁻¹ : (E d →L[ℝ] E d)ˣ) : E d →L[ℝ] E d) ξ)
    have hX : A x X = ξ := by
      have e1 : ((u : E d →L[ℝ] E d) * ↑u⁻¹) ξ = ξ := by rw [u.mul_inv]; rfl
      rw [hu] at e1; exact e1
    have h1 : ℓ X = ∑ j, ξ j * ξ j := by
      simp only [hℓ, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
        Pi.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply, smul_eq_mul, hX]
      rfl
    have h2 : ℓ X = 0 := by
      have := congrArg (fun L : 𝔤 →ₗ[ℝ] ℝ => L X) hℓ0
      simpa using this
    apply hξ
    have hs : ∑ j, ξ j * ξ j = 0 := h1.symm.trans h2
    ext j
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (ξ j))).1 hs j
      (Finset.mem_univ _)
    simpa using mul_self_eq_zero.1 this
  · intro f hf X x hx
    have hx1 : x ∈ Metric.ball (0 : E d) r₁ := Metric.ball_subset_ball (min_le_left _ _) hx
    have hxN : ((coordEquiv b x : 𝔤) : 𝔸) ∈ h.nhd := hball₁ hx1
    have hxS := h.nhd_subset hxN
    set φ : E d → ℂ := fun y => f (h.expG (coordEquiv b y)) with hφ
    have hφd : Differentiable ℝ φ := by
      have := h.contDiff_comp_coordEquiv hf 1 b
      simp only [one_mul] at this
      exact this.differentiable (by simp)
    have hev : (fun Y : 𝔤 => f (h.expG (coordEquiv b x) * h.expG Y)) =ᶠ[𝓝 0] φ ∘ psi b x := by
      filter_upwards [expG_psi h b x hxN] with Y hY
      simp [φ, hY]
    have hdiff : DifferentiableAt ℝ (psi b x) 0 := differentiableAt_psi b x hxS
    have key : h.rightDeriv X f (h.expG (coordEquiv b x)) = fderiv ℝ φ x (A x X) := by
      unfold IsExpLieAlgebra.rightDeriv
      rw [hev.fderiv_eq, fderiv_comp (0 : 𝔤) (by rw [psi_zero b x hxS]; exact hφd _) hdiff,
        psi_zero b x hxS]
      rfl
    rw [key]
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (A x X)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Complex.real_smul, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
    rfl

end GlobalTheory.ExpCoordFrame
