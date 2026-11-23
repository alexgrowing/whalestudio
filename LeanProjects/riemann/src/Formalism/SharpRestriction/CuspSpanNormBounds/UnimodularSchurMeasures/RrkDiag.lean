import Mathlib

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace

theorem rrk_diag {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SeparableSpace (Lp ℂ 2 ν)]
    (T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (hT : IsStarProjection T) {N : ℕ}
    (F : OrthonormalBasis (Fin N) ℂ (LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)))
    (κ : Y → Lp ℂ 2 ν) (hκ : ∀ f : Lp ℂ 2 ν, ∀ᵐ x ∂ν, (T f : Y → ℂ) x = ⟪κ x, f⟫_ℂ) :
    ∀ᵐ x ∂ν, ‖κ x‖ ^ 2 = ∑ w, ‖(((F w : LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)) : Lp ℂ 2 ν) : Y → ℂ) x‖ ^ 2 := by
  have hTT : ∀ f, T (T f) = T f := fun f => by
    have := hT.isIdempotentElem
    exact congrArg (fun S : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν => S f) this
  have hsym : ∀ f g : Lp ℂ 2 ν, ⟪T f, g⟫_ℂ = ⟪f, T g⟫_ℂ := fun f g => by
    have h := hT.isSelfAdjoint
    rw [ContinuousLinearMap.isSelfAdjoint_iff'] at h
    rw [← ContinuousLinearMap.adjoint_inner_right, h]
  set d : ℕ → Lp ℂ 2 ν := denseSeq (Lp ℂ 2 ν) with hd
  have h1 : ∀ᵐ x ∂ν, ∀ n, ⟪κ x, d n - T (d n)⟫_ℂ = 0 := by
    rw [ae_all_iff]
    intro n
    have hz : T (d n - T (d n)) = 0 := by rw [map_sub, hTT, sub_self]
    have h0 : ((T (d n - T (d n)) : Lp ℂ 2 ν) : Y → ℂ) =ᵐ[ν] 0 := by
      rw [hz]; exact Lp.coeFn_zero _ _ _
    filter_upwards [hκ (d n - T (d n)), h0] with x a1 a2
    rw [← a1, a2]; rfl
  have h2 : ∀ᵐ x ∂ν, ∀ w, (((F w : LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)) : Lp ℂ 2 ν) : Y → ℂ) x =
      ⟪κ x, ((F w : LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)) : Lp ℂ 2 ν)⟫_ℂ := by
    rw [ae_all_iff]
    intro w
    obtain ⟨u, hu⟩ := (F w).2
    have hfix : T ((F w : LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)) : Lp ℂ 2 ν) =
        ((F w : LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)) : Lp ℂ 2 ν) := by
      rw [← hu]; exact hTT u
    filter_upwards [hκ ((F w : LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)) : Lp ℂ 2 ν)] with x a1
    rw [← a1, hfix]
  filter_upwards [h1, h2] with x a1 a2
  have hall : ∀ f : Lp ℂ 2 ν, ⟪κ x, f - T f⟫_ℂ = 0 := by
    intro f
    have hc : Continuous fun f : Lp ℂ 2 ν => ⟪κ x, f - T f⟫_ℂ := by fun_prop
    have hcl : IsClosed {f : Lp ℂ 2 ν | ⟪κ x, f - T f⟫_ℂ = 0} := isClosed_eq hc continuous_const
    exact (denseRange_denseSeq (Lp ℂ 2 ν)).induction_on (p := fun f => ⟪κ x, f - T f⟫_ℂ = 0) f hcl a1
  have hfix : T (κ x) = κ x := by
    have e1 : ⟪κ x - T (κ x), κ x - T (κ x)⟫_ℂ = 0 := by
      rw [inner_sub_left, hall, hsym, map_sub, hTT, sub_self, inner_zero_right, sub_zero]
    have := inner_self_eq_zero.1 e1
    exact (sub_eq_zero.1 this).symm
  set v : LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν) := ⟨κ x, ⟨κ x, hfix⟩⟩ with hv
  have hp := F.sum_sq_norm_inner_right v
  have hn : ‖v‖ = ‖κ x‖ := rfl
  rw [← hn, ← hp]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [a2 w]
  have : ⟪F w, v⟫_ℂ = ⟪((F w : LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)) : Lp ℂ 2 ν), κ x⟫_ℂ := rfl
  rw [this, ← norm_inner_symm]

end Formalism.MainNotions.LeviCoordinates

end
