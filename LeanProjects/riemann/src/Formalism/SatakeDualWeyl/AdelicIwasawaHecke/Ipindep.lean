import Formalism.SatakeDualWeyl.Statement

noncomputable section

namespace Formalism.UG.P

open Formalism.UG

variable {G : Type} [Group G]

theorem mem_stabAt_mul_iff (Γ K : Subgroup G) (g : G) (γ : Γ) (κ : K) (δ : Γ) :
    δ ∈ stabAt Γ K ((γ : G) * g * κ) ↔ γ⁻¹ * δ * γ ∈ stabAt Γ K g := by
  simp only [stabAt, Set.mem_setOf_eq]
  have e : ((γ : G) * g * κ)⁻¹ * (δ : G) * ((γ : G) * g * κ) =
      (κ : G)⁻¹ * (g⁻¹ * ((γ⁻¹ * δ * γ : Γ) : G) * g) * κ := by
    push_cast; group
  rw [e, K.mul_mem_cancel_right κ.2, K.mul_mem_cancel_left (K.inv_mem κ.2)]

theorem card_stabAt_mul (Γ K : Subgroup G) (g : G) (γ : Γ) (κ : K) :
    Nat.card (stabAt Γ K ((γ : G) * g * κ)) = Nat.card (stabAt Γ K g) := by
  refine Nat.card_congr
    { toFun := fun δ => ⟨γ⁻¹ * δ.1 * γ, (mem_stabAt_mul_iff Γ K g γ κ δ.1).1 δ.2⟩
      invFun := fun δ => ⟨γ * δ.1 * γ⁻¹, (mem_stabAt_mul_iff Γ K g γ κ _).2 (by
        convert δ.2 using 2; group)⟩
      left_inv := fun δ => Subtype.ext (by group)
      right_inv := fun δ => Subtype.ext (by group) }

theorem inner_product_independent : Formalism.UG.IpIndep := by
  intro G _ Γ K k _ _ W _ _ ρ _ B hB s s' hs hs' _ f hf f' hf'
  have hf2 : ∀ (γ : Γ) (g : G) (κ : K), f ((γ : G) * g * κ) = ρ γ (f g) := hf
  have hf2' : ∀ (γ : Γ) (g : G) (κ : K), f' ((γ : G) * g * κ) = ρ γ (f' g) := hf'
  unfold ipAMF
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨γ, hγ, κ, hκ, he⟩ := (DoubleCoset.eq _ _ (s c) (s' c)).1 ((hs c).trans (hs' c).symm)
  have h1 : s' c = ((⟨γ, hγ⟩ : Γ) : G) * s c * ((⟨κ, hκ⟩ : K) : G) := he
  rw [h1, card_stabAt_mul, hf2, hf2', hB]

end Formalism.UG.P
