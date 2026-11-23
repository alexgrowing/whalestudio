import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockProductIsomorphism
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory

theorem exists_ne_zero_intertwiningMap_coind_of_doubleCoset :
    ∀ (G : Type) [Group G] [Finite G] (P P' : Subgroup G) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (σ : Representation ℂ P V) (σ' : Representation ℂ P' V') (x : G) (T : V →ₗ[ℂ] V'), T ≠ 0 → (∀ (p : P) (p' : P'), (p' : G) * x = x * (p : G) → σ' p' ∘ₗ T = T ∘ₗ σ p) → ∃ Φ : Representation.IntertwiningMap (Representation.coind P.subtype σ) (Representation.coind P'.subtype σ'), Φ ≠ 0 := by
  intro G _ _ P P' V V' _ _ _ _ σ σ' x T hT h
  classical
  haveI : Fintype P' := Fintype.ofFinite _
  let L : Representation.coindV P.subtype σ →ₗ[ℂ] Representation.coindV P'.subtype σ' :=
    { toFun := fun f => ⟨fun y => ∑ p' : P', σ' p' (T (f.1 (x⁻¹ * (p' : G)⁻¹ * y))), by
        intro q y
        beta_reduce
        rw [map_sum, ← Equiv.sum_comp (Equiv.mulLeft q)
          (fun p' : P' => σ' p' (T (f.1 (x⁻¹ * (p' : G)⁻¹ * (P'.subtype q * y)))))]
        refine Finset.sum_congr rfl fun p' _ => ?_
        simp [mul_assoc]⟩
      map_add' := fun f g => by
        ext y
        simp [Finset.sum_add_distrib]
      map_smul' := fun c f => by
        ext y
        simp [Finset.smul_sum] }
  have hL : ∀ f y, (L f).1 y = ∑ p' : P', σ' p' (T (f.1 (x⁻¹ * (p' : G)⁻¹ * y))) :=
    fun _ _ => rfl
  refine ⟨⟨L, fun g => ?_⟩, fun h0 => ?_⟩
  · ext f y
    change (L (Representation.coind P.subtype σ g f)).1 y = (L f).1 (y * g)
    rw [hL, hL]
    refine Finset.sum_congr rfl fun p' _ => ?_
    change σ' p' (T (f.1 (x⁻¹ * (p' : G)⁻¹ * y * g))) = _
    rw [mul_assoc _ y g]
  · obtain ⟨v, hv⟩ : ∃ v, T v ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hT (LinearMap.ext hc)
    let δ : Representation.coindV P.subtype σ :=
      ⟨fun y => if hy : y ∈ P then σ ⟨y, hy⟩ v else 0, by
        intro q y
        by_cases hy : y ∈ P
        · have hqy : P.subtype q * y ∈ P := P.mul_mem q.2 hy
          simp only [dif_pos hy, dif_pos hqy]
          rw [← Module.End.mul_apply, ← map_mul]
          rfl
        · have hqy : P.subtype q * y ∉ P := fun hh => hy ((P.mul_mem_cancel_left q.2).1 hh)
          simp only [dif_neg hy, dif_neg hqy, map_zero]⟩
    have hL0 : L = 0 := congrArg Representation.IntertwiningMap.toLinearMap h0
    have h1 : (L δ).1 x = 0 := by rw [hL0]; rfl
    have h2 : ∀ p' : P', σ' p' (T (δ.1 (x⁻¹ * (p' : G)⁻¹ * x))) =
        if x⁻¹ * (p' : G)⁻¹ * x ∈ P then T v else 0 := by
      intro p'
      by_cases hp : x⁻¹ * (p' : G)⁻¹ * x ∈ P
      · have hδ : δ.1 (x⁻¹ * (p' : G)⁻¹ * x) = σ ⟨_, hp⟩ v := dif_pos hp
        have := LinearMap.congr_fun (h ⟨_, hp⟩ p'⁻¹ (by simp [mul_assoc])) v
        simp only [LinearMap.comp_apply] at this
        rw [hδ, if_pos hp, ← this, ← Module.End.mul_apply, ← map_mul]
        simp
      · have hδ : δ.1 (x⁻¹ * (p' : G)⁻¹ * x) = 0 := dif_neg hp
        rw [hδ, if_neg hp]
        simp
    rw [hL, Finset.sum_congr rfl fun p' _ => h2 p', ← Finset.sum_filter, Finset.sum_const,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h1
    rcases h1 with h1 | h1
    · have : (1 : P') ∈ Finset.univ.filter fun p' : P' => x⁻¹ * (p' : G)⁻¹ * x ∈ P := by
        simp [P.one_mem]
      exact (Finset.card_pos.2 ⟨_, this⟩).ne' (Nat.cast_eq_zero.1 h1)
    · exact hv h1

end GlobalTheory
