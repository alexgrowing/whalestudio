import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec

namespace GlobalTheory.UnipKill

open ReciprocityTheory.ChartRestriction.G.FD NumberField

theorem isUStab_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    {G : Matrix (Fin N) (Fin N) E} {Λ : Submodule (𝓞 E) (Fin N → E)} {g g' : GL (Fin N) E}
    (hg : IsUStab G Λ g) (hg' : IsUStab G Λ g') : IsUStab G Λ (g * g') := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hg.1, hg'.1]
  · rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hg'.2, hg.2]

theorem isUStab_one {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    (G : Matrix (Fin N) (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E)) :
    IsUStab G Λ (1 : GL (Fin N) E) := by
  refine ⟨fun x y => ?_, fun x => ?_⟩ <;> simp

theorem isUStab_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    {G : Matrix (Fin N) (Fin N) E} {Λ : Submodule (𝓞 E) (Fin N → E)} {g : GL (Fin N) E}
    (hg : IsUStab G Λ g) (n : ℕ) : IsUStab G Λ (g ^ n) := by
  induction n with
  | zero => simpa using isUStab_one G Λ
  | succ n ih => rw [pow_succ]; exact isUStab_mul ih hg

theorem pow_mem_of_isUStab : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (X : Data E N) (g : GL (Fin N) E), IsUStab X.Gm X.Λ g → ∃ k : ℕ, 0 < k ∧ g ^ k ∈ X.Γ := by
  intro E _ _ _ N X g hg
  obtain ⟨S, hS⟩ := X.Γ_index
  have h : ∀ n : ℕ, ∃ s : S, (s : GL (Fin N) E)⁻¹ * g ^ n ∈ X.Γ := fun n => by
    obtain ⟨s, hs, hmem⟩ := hS _ (isUStab_pow hg n)
    exact ⟨⟨s, hs⟩, hmem⟩
  choose f hf using h
  obtain ⟨a, b, hab, hfab⟩ := Finite.exists_ne_map_eq_of_infinite f
  have key : ∀ a b : ℕ, a < b → f a = f b → ∃ k : ℕ, 0 < k ∧ g ^ k ∈ X.Γ := by
    intro a b hlt hf'
    refine ⟨b - a, Nat.sub_pos_of_lt hlt, ?_⟩
    have h1 := X.Γ.mul_mem (X.Γ.inv_mem (hf a)) (hf b)
    rw [hf'] at h1
    have : ((f b : GL (Fin N) E)⁻¹ * g ^ a)⁻¹ * ((f b : GL (Fin N) E)⁻¹ * g ^ b) = g ^ (b - a) := by
      rw [mul_inv_rev, inv_inv, mul_assoc, ← mul_assoc (f b : GL (Fin N) E), mul_inv_cancel,
        one_mul, ← Nat.add_sub_cancel' hlt.le, pow_add, ← mul_assoc, inv_mul_cancel, one_mul,
        Nat.add_sub_cancel_left]
    rwa [this] at h1
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b h hfab
  · exact key b a h hfab.symm

end GlobalTheory.UnipKill
