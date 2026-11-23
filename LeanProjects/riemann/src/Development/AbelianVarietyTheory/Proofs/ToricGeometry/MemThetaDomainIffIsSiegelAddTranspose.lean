import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe

open Complex Matrix Filter Topology ReciprocityTheory.PTheta

namespace GlobalTheory

variable {ι : Type*} [Fintype ι]

theorem siegelH_subset_thetaDomain : SiegelH ι ⊆ ThetaDomain ι := by
  intro τ hτ
  obtain ⟨hs, hp⟩ := hτ
  have ht : (τ.map Complex.im)ᵀ = τ.map Complex.im := by
    rw [← Matrix.transpose_map, hs.eq]
  show (τ.map Complex.im + (τ.map Complex.im)ᵀ).PosDef
  rw [ht]
  exact hp.add hp

theorem isOpen_thetaDomain : IsOpen (ThetaDomain ι) := by
  set S : Matrix ι ι ℂ → Matrix ι ι ℝ :=
    fun τ => τ.map Complex.im + (τ.map Complex.im)ᵀ with hS
  have hherm : ∀ τ, (S τ).IsHermitian := by
    intro τ
    ext i j
    simp [hS, add_comm]
  have hscale : ∀ τ (c : ℝ) (x : ι → ℝ),
      (c • x) ⬝ᵥ (S τ *ᵥ (c • x)) = c * c * (x ⬝ᵥ (S τ *ᵥ x)) := by
    intro τ c x
    simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  have key : ∀ τ, τ ∈ ThetaDomain ι ↔
      ∀ x ∈ Metric.sphere (0 : ι → ℝ) 1, 0 < x ⬝ᵥ (S τ *ᵥ x) := by
    intro τ
    change (S τ).PosDef ↔ _
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    simp only [star_trivial]
    constructor
    · rintro ⟨-, h⟩ x hx
      apply h
      rintro rfl
      simp at hx
    · intro h
      refine ⟨hherm τ, fun x hx => ?_⟩
      have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hy : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : ι → ℝ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
          inv_mul_cancel₀ hn.ne']
      have h1 := h _ hy
      rw [hscale] at h1
      by_contra hle
      have : ‖x‖⁻¹ * ‖x‖⁻¹ * (x ⬝ᵥ (S τ *ᵥ x)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.mp hle)
      linarith
  have hcont : Continuous fun p : Matrix ι ι ℂ × (ι → ℝ) => p.2 ⬝ᵥ (S p.1 *ᵥ p.2) := by
    have hm : Continuous fun p : Matrix ι ι ℂ × (ι → ℝ) => p.1.map Complex.im :=
      continuous_fst.matrix_map Complex.continuous_im
    exact continuous_snd.dotProduct ((hm.add hm.matrix_transpose).matrix_mulVec continuous_snd)
  rw [isOpen_iff_eventually]
  intro τ₀ h₀
  have hev : ∀ᶠ τ in 𝓝 τ₀, ∀ x ∈ Metric.sphere (0 : ι → ℝ) 1, 0 < x ⬝ᵥ (S τ *ᵥ x) := by
    refine (isCompact_sphere (0 : ι → ℝ) 1).eventually_forall_of_forall_eventually
      (P := fun τ x => 0 < x ⬝ᵥ (S τ *ᵥ x)) fun x hx => ?_
    exact (hcont.continuousAt (x := (τ₀, x))).eventually (lt_mem_nhds ((key τ₀).1 h₀ x hx))
  filter_upwards [hev] with τ hτ
  exact (key τ).2 hτ

theorem siegelSubDomain_and_domainOpen : SiegelSubDomainStatement ∧ DomainOpenStatement := by
  refine ⟨fun κ _ => siegelH_subset_thetaDomain, fun κ _ => ?_⟩
  exact isOpen_thetaDomain

end GlobalTheory
