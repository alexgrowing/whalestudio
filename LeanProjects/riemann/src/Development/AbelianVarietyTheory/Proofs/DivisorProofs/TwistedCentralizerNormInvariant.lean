import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open scoped Classical

namespace GlobalTheory.LKMid.TwCent

open GlobalTheory.LKMid

variable {H : Type} [Group H] (θ : H →* H)

theorem nrmG_succ' (j : ℕ) (δ : H) : nrmG θ (j + 1) δ = nrmG θ j δ * (⇑θ)^[j] δ := by
  simp [nrmG, List.range_succ, List.map_append, List.prod_append]

theorem mul_map_nrmG (j : ℕ) (δ : H) : δ * θ (nrmG θ j δ) = nrmG θ (j + 1) δ := by
  induction j with
  | zero => simp [nrmG]
  | succ j ih =>
    rw [nrmG_succ' θ (j + 1), nrmG_succ', map_mul, ← mul_assoc, ih, ← Function.iterate_succ_apply' (⇑θ), nrmG_succ' θ j]

theorem iterate_twConj (δ : H) (i : ℕ) (h : H) :
    (⇑((MulAut.conj δ).toMonoidHom.comp θ))^[i] h = nrmG θ i δ * (⇑θ)^[i] h * (nrmG θ i δ)⁻¹ := by
  induction i with
  | zero => simp [nrmG]
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply' (⇑θ), ← mul_map_nrmG]
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      map_mul, map_inv, mul_inv_rev, inv_inv]
    group

theorem main : ∀ {H : Type} [Group H] (θ : H →* H) (δ : H) (r : ℕ), 0 < r → (∀ h, (⇑θ)^[r] h = h) →
    (∀ z ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}, δ * θ z * δ⁻¹ ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}) ∧
    (∀ z ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}, (⇑((MulAut.conj δ).toMonoidHom.comp θ))^[r] z = z) := by
  intro H _ θ δ r _ hθ
  have key : δ * θ (nrmG θ r δ) = nrmG θ r δ * δ := by
    rw [mul_map_nrmG, nrmG_succ', hθ]
  have hN : nrmG θ r δ = δ * θ (nrmG θ r δ) * δ⁻¹ := by rw [key]; group
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    have h2 : θ (nrmG θ r δ) * θ z = θ z * θ (nrmG θ r δ) := by rw [← map_mul, ← hz, map_mul]
    symm
    calc nrmG θ r δ * (δ * θ z * δ⁻¹) = δ * (θ (nrmG θ r δ) * θ z) * δ⁻¹ := by
          conv_lhs => rw [hN]
          group
      _ = δ * (θ z * θ (nrmG θ r δ)) * δ⁻¹ := by rw [h2]
      _ = δ * θ z * δ⁻¹ * nrmG θ r δ := by
          conv_rhs => rw [hN]
          group
  · rw [Subgroup.mem_centralizer_singleton_iff] at hz
    rw [iterate_twConj, hθ, ← hz, mul_inv_cancel_right]

end GlobalTheory.LKMid.TwCent
