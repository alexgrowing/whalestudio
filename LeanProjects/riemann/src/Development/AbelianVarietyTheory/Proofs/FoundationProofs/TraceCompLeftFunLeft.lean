import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
open Polynomial Classical GlobalTheory.BadShare

noncomputable section
namespace GlobalTheory.BadShare

theorem trace_compLeft_funLeft {G W : Type} [Fintype G] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A : W →ₗ[ℂ] W) (f : G → G) :
    LinearMap.trace ℂ (G → W) (A.compLeft G ∘ₗ LinearMap.funLeft ℂ W f) =
      ∑ x, if f x = x then LinearMap.trace ℂ W A else 0 := by
  have h : A.compLeft G ∘ₗ LinearMap.funLeft ℂ W f =
      ∑ x, LinearMap.single ℂ (fun _ : G => W) x ∘ₗ (A ∘ₗ LinearMap.proj (f x)) := by
    refine LinearMap.ext fun φ => funext fun y => ?_
    simp [LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply, LinearMap.funLeft_apply]
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [LinearMap.trace_comp_comm']
  split_ifs with hx
  · congr 1
    ext w
    simp [hx]
  · have : (A ∘ₗ LinearMap.proj (f x)) ∘ₗ LinearMap.single ℂ (fun _ : G => W) x = 0 := by
      ext w
      simp [hx]
    rw [this, map_zero]

section
variable {G : Type} [Group G] [Fintype G] {Γ : Type} [Group Γ] [Fintype Γ] (r : Γ →* G)
  {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (σ : Representation ℂ Γ W)

def coindSum : (G → W) →ₗ[ℂ] Representation.coindV r σ :=
  LinearMap.codRestrict _
    (∑ γ : Γ, (σ γ⁻¹ : W →ₗ[ℂ] W).compLeft G ∘ₗ LinearMap.funLeft ℂ W fun x => r γ * x) (by
      intro φ δ x
      simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.comp_apply, LinearMap.compLeft_apply,
        Function.comp_apply, LinearMap.funLeft_apply, map_sum]
      refine Fintype.sum_equiv (Equiv.mulRight δ) _ _ fun γ => ?_
      simp only [Equiv.coe_mulRight, map_mul r, mul_assoc, mul_inv_rev]
      rw [← Module.End.mul_apply, ← map_mul σ, mul_inv_cancel_left])

omit [Fintype G] [FiniteDimensional ℂ W] in
theorem coindSum_apply (φ : G → W) (x : G) :
    (coindSum r σ φ).1 x = ∑ γ : Γ, σ γ⁻¹ (φ (r γ * x)) := by
  change (∑ γ : Γ, (σ γ⁻¹ : W →ₗ[ℂ] W).compLeft G ∘ₗ LinearMap.funLeft ℂ W fun x => r γ * x) φ x = _
  simp [LinearMap.sum_apply, Finset.sum_apply, LinearMap.funLeft_apply]

theorem trace_coind_mul_card (g : G) :
    LinearMap.trace ℂ _ (Representation.coind r σ g) * (Fintype.card Γ : ℂ) =
      ∑ γ : Γ, ∑ x : G, if r γ * (x * g) = x then LinearMap.trace ℂ W (σ γ⁻¹) else 0 := by
  have h1 : (Fintype.card Γ : ℂ) • (Representation.coind r σ g : _ →ₗ[ℂ] _) =
      coindSum r σ ∘ₗ (LinearMap.funLeft ℂ W (fun x => x * g) ∘ₗ (Representation.coindV r σ).subtype) := by
    refine LinearMap.ext fun φ => Subtype.ext (funext fun x => ?_)
    rw [LinearMap.comp_apply, coindSum_apply]
    have : ∀ γ : Γ, σ γ⁻¹ ((LinearMap.funLeft ℂ W (fun x => x * g) ∘ₗ (Representation.coindV r σ).subtype) φ (r γ * x))
        = φ.1 (x * g) := by
      intro γ
      change σ γ⁻¹ (φ.1 (r γ * x * g)) = _
      rw [mul_assoc, φ.2 γ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [Finset.sum_congr rfl fun γ _ => this γ, Finset.sum_const, Finset.card_univ]
    change (Fintype.card Γ : ℂ) • φ.1 (x * g) = _
    rw [Nat.cast_smul_eq_nsmul]
  have h2 : (LinearMap.funLeft ℂ W (fun x => x * g) ∘ₗ (Representation.coindV r σ).subtype) ∘ₗ coindSum r σ =
      ∑ γ : Γ, (σ γ⁻¹ : W →ₗ[ℂ] W).compLeft G ∘ₗ LinearMap.funLeft ℂ W fun x => r γ * (x * g) := by
    refine LinearMap.ext fun φ => funext fun x => ?_
    change (coindSum r σ φ).1 (x * g) = _
    rw [coindSum_apply]
    simp [LinearMap.sum_apply, Finset.sum_apply, LinearMap.funLeft_apply]
  rw [mul_comm, ← smul_eq_mul, ← map_smul, h1, LinearMap.trace_comp_comm', h2, map_sum]
  exact Finset.sum_congr rfl fun γ _ => trace_compLeft_funLeft _ _

end

end GlobalTheory.BadShare
