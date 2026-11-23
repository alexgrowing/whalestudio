import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory

theorem reduction_ker_uniformiser_eq_range_pow : ∀ (p : ℕ) (W k Λ : Type) [CommRing W] [IsDomain W] [Field k] [CommRing Λ] (h e : ℕ) (c : W →+* k) (ρ : Λ →+* Matrix (Fin h) (Fin h) W) (π : Λ) (u : Λˣ), (p : W) ≠ 0 → Function.Surjective c → (∀ w, c w = 0 → (p : W) ∣ w) → c p = 0 → 0 < e → (p : Λ) = π ^ e * u → ((ρ π).map c) ^ e = 0 ∧ ∀ x : Fin h → k, (ρ π).map c *ᵥ x = 0 → ∃ y, x = ((ρ π).map c) ^ (e - 1) *ᵥ y := by
  intro p W k Λ _ _ _ _ h e c ρ π u hp hc hker hcp he hpu
  have hmap : ∀ M : Matrix (Fin h) (Fin h) W, M.map c = c.mapMatrix M := fun M => rfl
  have key : ρ π * ρ (π ^ (e - 1) * ↑u) = (p : Matrix (Fin h) (Fin h) W) := by
    rw [← map_mul, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel he, ← hpu, map_natCast]
  have key' : ρ (π ^ (e - 1) * ↑u) * ρ π = (p : Matrix (Fin h) (Fin h) W) := by
    rw [← map_mul, mul_comm, map_mul, key]
  have hpv : ∀ v : Fin h → W, (p : Matrix (Fin h) (Fin h) W) *ᵥ v = (p : W) • v := by
    intro v
    exact Matrix.natCast_mulVec p v
  have hpk : (p : k) = 0 := by rw [← map_natCast c]; exact hcp
  refine ⟨?_, ?_⟩
  · have hpe : π ^ e = (p : Λ) * ↑u⁻¹ := by
      rw [hpu, mul_assoc, Units.mul_inv, mul_one]
    rw [hmap, ← map_pow, ← map_pow, hpe, map_mul, map_mul, map_natCast, map_natCast,
      ← map_natCast (algebraMap k (Matrix (Fin h) (Fin h) k)) p, hpk, map_zero, zero_mul]
  · intro x hx
    choose xt hxt using fun i => hc (x i)
    have hcx : c ∘ xt = x := funext hxt
    have hdiv : ∀ i, (p : W) ∣ (ρ π *ᵥ xt) i := by
      intro i; apply hker
      rw [RingHom.map_mulVec, hcx, hx]; rfl
    choose z hz using hdiv
    have hinj : ∀ v : Fin h → W, ρ π *ᵥ v = 0 → v = 0 := by
      intro v hv
      have h1 : (p : W) • v = 0 := by
        rw [← hpv, ← key', ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
      exact (smul_eq_zero.mp h1).resolve_left hp
    have hxtz : ρ π *ᵥ xt = (p : W) • z := funext fun i => by rw [hz i]; rfl
    have hxB : xt = (ρ π ^ (e - 1)) *ᵥ (ρ ↑u *ᵥ z) := by
      rw [Matrix.mulVec_mulVec, ← map_pow, ← map_mul]
      apply sub_eq_zero.mp
      apply hinj
      rw [Matrix.mulVec_sub, hxtz, Matrix.mulVec_mulVec, key, hpv, sub_self]
    refine ⟨c ∘ (ρ ↑u *ᵥ z), ?_⟩
    funext i
    rw [hmap, ← map_pow, ← hxt i, hxB, RingHom.map_mulVec]
    rfl

end GlobalTheory
