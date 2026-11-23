import Mathlib
import GroundTheory.AutomorphicForms.UnitaryRepresentations.IsInvariantIffCommuteStarProjection

namespace GroundTheory.Automorphic

namespace UnitaryRep

open scoped InnerProductSpace ENNReal
open ContinuousLinearMap

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]

section directSum

variable (ρ : ∀ i, UnitaryRep G (E i))

lemma memℓp_map (g : G) (x : lp E 2) : Memℓp (fun i => ρ i g (x i)) 2 := by
  apply memℓp_norm_iff.mp
  have : (fun i => ‖ρ i g (x i)‖) = fun i => ‖x i‖ := funext fun i => norm_map _ _ _
  rw [this]
  exact memℓp_norm_iff.mpr (lp.memℓp x)

noncomputable def hilbertDirectSumIsometry (g : G) : lp E 2 ≃ₗᵢ[ℂ] lp E 2 where
  toFun x := ⟨fun i => ρ i g (x i), memℓp_map ρ g x⟩
  invFun x := ⟨fun i => ρ i g⁻¹ (x i), memℓp_map ρ g⁻¹ x⟩
  map_add' x y := lp.ext (funext fun i => by simp; rfl)
  map_smul' c x := lp.ext (funext fun i => by simp)
  left_inv x := lp.ext (funext fun i => by simp)
  right_inv x := lp.ext (funext fun i => by simp)
  norm_map' x := by
    have hp : 0 < (2 : ℝ≥0∞).toReal := by simp
    rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
    congr 2
    ext i
    change ‖ρ i g (x i)‖ ^ _ = _
    rw [norm_map]

lemma hilbertDirectSumIsometry_apply (g : G) (x : lp E 2) (i : ι) :
    hilbertDirectSumIsometry ρ g x i = ρ i g (x i) := rfl

noncomputable def directSumHom : G →* (lp E 2 ≃ₗᵢ[ℂ] lp E 2) where
  toFun := hilbertDirectSumIsometry ρ
  map_one' := LinearIsometryEquiv.ext fun x => lp.ext (funext fun i => by
    simp [hilbertDirectSumIsometry_apply])
  map_mul' g h := LinearIsometryEquiv.ext fun x => lp.ext (funext fun i => by
    change ρ i (g * h) (x i) = ρ i g (ρ i h (x i))
    exact map_mul_apply _ g h _)

omit [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)] in
lemma summable_norm_mul_norm (x y : lp E 2) : Summable fun i => ‖x i‖ * ‖y i‖ := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by simp
  have hx := (lp.memℓp x).summable hp
  have hy := (lp.memℓp y).summable hp
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hx hy
  refine Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun i => ?_) (hx.add hy)
  nlinarith [sq_nonneg (‖x i‖ - ‖y i‖), norm_nonneg (x i), norm_nonneg (y i)]

noncomputable def directSum : UnitaryRep G (lp E 2) where
  toHom := (Unitary.linearIsometryEquiv (𝕜 := ℂ) (H := lp E 2)).symm.toMonoidHom.comp
    (directSumHom ρ)
  continuous_orbit' := continuous_of_weak _ fun x y => by
    have e : ∀ g, ⟪(((Unitary.linearIsometryEquiv (𝕜 := ℂ) (H := lp E 2)).symm.toMonoidHom.comp
        (directSumHom ρ) g : unitary (lp E 2 →L[ℂ] lp E 2)) : lp E 2 →L[ℂ] lp E 2) x, y⟫_ℂ =
        ∑' i, ⟪ρ i g (x i), y i⟫_ℂ := fun g => by
      rw [lp.inner_eq_tsum]
      rfl
    simp_rw [e]
    refine continuous_tsum (fun i => (ρ i).continuous_inner_orbit (x i) (y i))
      (summable_norm_mul_norm x y) (fun i g => ?_)
    calc ‖⟪ρ i g (x i), y i⟫_ℂ‖ ≤ ‖ρ i g (x i)‖ * ‖y i‖ := norm_inner_le_norm _ _
      _ = ‖x i‖ * ‖y i‖ := by rw [norm_map]

@[simp] lemma directSum_apply (g : G) (x : lp E 2) (i : ι) :
    directSum ρ g x i = ρ i g (x i) := rfl

noncomputable def singleL [DecidableEq ι] (i : ι) : E i →L[ℂ] lp E 2 :=
  LinearMap.mkContinuous (lp.lsingle 2 i) 1 fun a => by
    rw [one_mul, lp.lsingle_apply]
    exact (lp.norm_single (by norm_num) i a).le

omit [∀ i, CompleteSpace (E i)] in
lemma singleL_apply [DecidableEq ι] (i : ι) (a : E i) : singleL i a = lp.single 2 i a := rfl

theorem singleL_mem_intertwiners [DecidableEq ι] (i : ι) :
    singleL i ∈ (ρ i).intertwiners (directSum ρ) := by
  intro g a
  refine lp.ext (funext fun j => ?_)
  rw [singleL_apply, directSum_apply, singleL_apply]
  by_cases h : j = i
  · subst h
    simp
  · rw [lp.single_apply_ne 2 i _ h, lp.single_apply_ne 2 i _ h, map_zero]

end directSum

noncomputable def equivDirectSumOfIsHilbertSum {π : UnitaryRep G H} {V : ι → Submodule ℂ H}
    [∀ i, CompleteSpace (V i)] (hinv : ∀ i, π.IsInvariant (V i))
    (hV : IsHilbertSum ℂ (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    π.Equiv (directSum fun i => π.restrict (V i) (hinv i)) where
  toLinearIsometryEquiv := hV.linearIsometryEquiv
  map_apply' g v := by
    apply hV.linearIsometryEquiv.symm.injective
    rw [LinearIsometryEquiv.symm_apply_apply, hV.linearIsometryEquiv_symm_apply]
    conv_lhs => rw [← hV.linearIsometryEquiv.symm_apply_apply v,
      hV.linearIsometryEquiv_symm_apply,
      (π g).map_tsum (hV.OrthogonalFamily.summable_of_lp _)]
    rfl

theorem isEquivalent_directSum_of_isHilbertSum {π : UnitaryRep G H} {V : ι → Submodule ℂ H}
    [∀ i, CompleteSpace (V i)] (hinv : ∀ i, π.IsInvariant (V i))
    (hV : IsHilbertSum ℂ (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    π.IsEquivalent (directSum fun i => π.restrict (V i) (hinv i)) :=
  ⟨equivDirectSumOfIsHilbertSum hinv hV⟩

end UnitaryRep

end GroundTheory.Automorphic
