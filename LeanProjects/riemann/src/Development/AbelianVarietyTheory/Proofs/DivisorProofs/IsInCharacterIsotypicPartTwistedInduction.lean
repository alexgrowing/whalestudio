import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.IndIso

theorem sum_dite_mem {G M : Type} [Group G] [Fintype G] [AddCommMonoid M] (H : Subgroup G)
    (f : H → M) : ∑ z : G, (if h : z ∈ H then f ⟨z, h⟩ else 0) = ∑ h : H, f h := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun z => z ∈ H)]
  have h2 : ∑ i : {x // ¬ x ∈ H}, (if h : (i : G) ∈ H then f ⟨i, h⟩ else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => dif_neg i.2
  rw [h2, add_zero]
  exact Fintype.sum_congr _ _ fun i => dif_pos i.2

theorem star_ext_zero {G : Type} [Group G] (H : Subgroup G) (c : H → ℂ) (z : G) :
    star (ext0 H c z) = ext0 H (fun h => star (c h)) z := by
  unfold ext0; split_ifs <;> simp

theorem reidx {G M : Type} [Group G] [Fintype G] [AddCommMonoid M] [Module ℂ M] (H : Subgroup G)
    (a b : G) (c : H → ℂ) (T : G → M) :
    ∑ x : G, ext0 H c (a * x * b) • T x = ∑ h : H, c h • T (a⁻¹ * h * b⁻¹) := by
  rw [Fintype.sum_equiv ((Equiv.mulLeft a).trans (Equiv.mulRight b)) _
    (fun z => ext0 H c z • T (a⁻¹ * z * b⁻¹)) (fun x => by simp [mul_assoc])]
  rw [← sum_dite_mem H (fun h => c h • T (a⁻¹ * h * b⁻¹))]
  refine Fintype.sum_congr _ _ fun z => ?_
  unfold ext0; split_ifs <;> simp

end GlobalTheory.Shin.IndIso

namespace GlobalTheory.Shin.IndIso

theorem kills_ind : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (τ : G → G) (φ Y : H → ℂ), Kills φ Y →
    Kills (fun x => (Nat.card H : ℂ)⁻¹ * ∑ᶠ y : G, ext0 H φ (y⁻¹ * x * τ y)) (ind H Y) := by
  intro G _ _ H τ φ Y hK V _ _ _ ρ hρ
  letI : Fintype G := Fintype.ofFinite G
  have hHc : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hGc : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'

  have hres : ∑ᶠ h : H, star (Y h) * LinearMap.trace ℂ V ((ρ.comp H.subtype) h) = 0 := by
    rw [finsum_eq_sum_of_fintype]
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    simp only [ind, finsum_eq_sum_of_fintype, star_mul', star_inv₀, star_natCast, star_sum, star_ext_zero] at hρ
    simp only [mul_assoc, ← Finset.mul_sum] at hρ
    have hρ' := (mul_eq_zero.mp hρ).resolve_left (inv_ne_zero hHc)
    have trc : ∀ g x : G, LinearMap.trace ℂ V (ρ (g * (x * g⁻¹))) = LinearMap.trace ℂ V (ρ x) := by
      intro g x
      rw [map_mul ρ, map_mul ρ, LinearMap.trace_mul_comm, mul_assoc, ← map_mul ρ, ← map_mul ρ]
      simp
    simp only [Finset.sum_mul] at hρ'
    rw [Finset.sum_comm] at hρ'
    have key : ∀ g : G, ∑ x : G, ext0 H (fun h => star (Y h)) (g⁻¹ * (x * g)) * LinearMap.trace ℂ V (ρ x)
        = ∑ h : H, star (Y h) * LinearMap.trace ℂ V (ρ h) := by
      intro g
      have := reidx (M := ℂ) H g⁻¹ g (fun h => star (Y h)) (fun x => LinearMap.trace ℂ V (ρ x))
      simp only [smul_eq_mul, inv_inv, mul_assoc] at this
      rw [this]
      exact Fintype.sum_congr _ _ fun h => by rw [trc]
    simp only [key, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hρ'
    rw [← Nat.card_eq_fintype_card] at hρ'
    exact (mul_eq_zero.mp hρ').resolve_left hGc
  have hk := hK V (ρ.comp H.subtype) hres
  rw [finsum_eq_sum_of_fintype] at hk
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at hk

  rw [finsum_eq_sum_of_fintype]
  simp only [finsum_eq_sum_of_fintype, star_mul', star_inv₀, star_natCast, star_sum, star_ext_zero, mul_smul,
    Finset.sum_smul]
  rw [← Finset.smul_sum, Finset.sum_comm]
  have key2 : ∀ y : G, ∑ x : G, ext0 H (fun h => star (φ h)) (y⁻¹ * x * τ y) • ρ x = 0 := by
    intro y
    rw [reidx H y⁻¹ (τ y) (fun h => star (φ h)) (fun x => ρ x)]
    simp only [inv_inv, map_mul]
    have : ∑ h : H, star (φ h) • (ρ y * ρ h * ρ (τ y)⁻¹) = ρ y * (∑ h : H, star (φ h) • ρ h) * ρ (τ y)⁻¹ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Fintype.sum_congr _ _ fun h => ?_
      rw [mul_smul_comm, smul_mul_assoc]
    rw [this, hk, mul_zero, zero_mul]
  simp only [key2, Finset.sum_const_zero, smul_zero]

end GlobalTheory.Shin.IndIso
