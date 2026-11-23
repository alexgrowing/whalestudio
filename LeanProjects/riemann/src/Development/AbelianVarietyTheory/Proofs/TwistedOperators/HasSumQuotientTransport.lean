import Mathlib

namespace GlobalTheory

theorem hasSum_quotient_transport :
    ∀ (G H : Type) [Group G] [Group H] (e : G ≃* H) (K : Subgroup G) (K' : Subgroup H),
      (∀ g, g ∈ K ↔ e g ∈ K') → ∀ f : G → ℂ, (∀ g, ∀ k ∈ K, f (g * k) = f g) → ∀ s : ℂ,
      HasSum (fun b : H ⧸ K' => f (e.symm b.out)) s → HasSum (fun a : G ⧸ K => f a.out) s := by
  intro G H _ _ e K K' hK f hf s hs
  have hrel : ∀ a b : G, (QuotientGroup.leftRel K) a b ↔ (QuotientGroup.leftRel K') (e a) (e b) := by
    intro a b
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, hK, map_mul, map_inv]

  let ψ : G ⧸ K ≃ H ⧸ K' := Quotient.congr e.toEquiv hrel
  have hψ : ∀ q : G ⧸ K, f (e.symm (ψ q).out) = f q.out := by
    intro q
    have h2 : ψ q = QuotientGroup.mk (e q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have h3 : (e q.out)⁻¹ * (ψ q).out ∈ K' := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq', h2]
    have h4 : e.symm (ψ q).out = q.out * e.symm ((e q.out)⁻¹ * (ψ q).out) := by
      rw [map_mul, map_inv, MulEquiv.symm_apply_apply, mul_inv_cancel_left]
    rw [h4, hf _ _ ((hK _).2 (by simpa using h3))]
  have hcomp : (fun a : G ⧸ K => f a.out) = (fun b : H ⧸ K' => f (e.symm b.out)) ∘ ψ := by
    funext q
    exact (hψ q).symm
  rw [hcomp]
  exact (Equiv.hasSum_iff ψ).2 hs

end GlobalTheory
