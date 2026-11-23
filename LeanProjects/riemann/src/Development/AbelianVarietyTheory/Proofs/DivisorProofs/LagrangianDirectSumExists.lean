import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped Matrix

namespace GlobalTheory

def lagrangianDoublingMap (F : Type) [Field F] (κ : Type) :
    ((κ → F) × (κ → F)) × ((κ → F) × (κ → F)) →ₗ[F] (κ ⊕ κ → F) × (κ ⊕ κ → F) where
  toFun p := (Sum.elim p.1.1 p.2.1, Sum.elim p.1.2 (-p.2.2))
  map_add' p q := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> cases i <;> simp [add_comm]
  map_smul' c p := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> cases i <;> simp

theorem lagrangianDoublingMap_injective (F : Type) [Field F] (κ : Type) :
    Function.Injective (lagrangianDoublingMap F κ) := by
  intro p q h
  simp only [lagrangianDoublingMap, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have a1 : p.1.1 = q.1.1 := funext fun i => by simpa using congrFun h1 (Sum.inl i)
  have b1 : p.2.1 = q.2.1 := funext fun i => by simpa using congrFun h1 (Sum.inr i)
  have a2 : p.1.2 = q.1.2 := funext fun i => by simpa using congrFun h2 (Sum.inl i)
  have b2 : p.2.2 = q.2.2 := funext fun i => by simpa using congrFun h2 (Sum.inr i)
  exact Prod.ext (Prod.ext a1 a2) (Prod.ext b1 b2)

theorem lagrangian_doubling_exists {F : Type} [Field F] {κ : Type} [Fintype κ]
    (L₀ : Submodule F ((κ → F) × (κ → F))) :
    (∀ a ∈ L₀, ∀ b ∈ L₀, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) → Module.finrank F L₀ = Fintype.card κ →
    ∃ L : Submodule F ((κ ⊕ κ → F) × (κ ⊕ κ → F)), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
      Module.finrank F L = Fintype.card (κ ⊕ κ) ∧
      ∀ w ∈ L, ∃ a ∈ L₀, ∃ b ∈ L₀, w = (Sum.elim a.1 b.1, Sum.elim a.2 (-b.2)) := by
  intro hiso hrk
  let g : (L₀ × L₀) →ₗ[F] (κ ⊕ κ → F) × (κ ⊕ κ → F) :=
    (lagrangianDoublingMap F κ).comp (L₀.subtype.prodMap L₀.subtype)
  have hg : ∀ p : L₀ × L₀, g p =
      (Sum.elim (p.1 : (κ → F) × (κ → F)).1 (p.2 : (κ → F) × (κ → F)).1,
        Sum.elim (p.1 : (κ → F) × (κ → F)).2 (-(p.2 : (κ → F) × (κ → F)).2)) := fun p => rfl
  have ginj : Function.Injective g := by
    intro p q h
    have := lagrangianDoublingMap_injective F κ h
    simp only [LinearMap.prodMap_apply, Submodule.coe_subtype, Prod.mk.injEq] at this
    exact Prod.ext (Subtype.ext this.1) (Subtype.ext this.2)
  refine ⟨LinearMap.range g, ?_, ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    rw [hg, hg]
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply,
      mul_neg, Finset.sum_neg_distrib]
    have h1 := hiso _ p.1.2 _ q.1.2
    have h2 := hiso _ p.2.2 _ q.2.2
    simp only [dotProduct] at h1 h2
    rw [h1, h2]
  · rw [LinearMap.finrank_range_of_inj ginj, Module.finrank_prod, hrk, Fintype.card_sum]
  · rintro _ ⟨p, rfl⟩
    exact ⟨p.1, p.1.2, p.2, p.2.2, hg p⟩

end GlobalTheory
