import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.KillsMuOrd

theorem pow_apply_of_apply {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : G ℚ Ω) (ζ : Ω) (k : ℕ)
    (h : s ζ = ζ ^ k) : ∀ n : ℕ, (s ^ n) ζ = ζ ^ (k ^ n) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, h, ← pow_mul, pow_succ', mul_comm]

theorem pow_fixes {Ω : Type} [Field Ω] [Algebra ℚ Ω] (l : ℕ) [hl : Fact l.Prime] (s : G ℚ Ω) (ζ : Ω)
    (hζ : ζ ^ l = 1) : (s ^ (l - 1)) ζ = ζ := by
  by_cases h1 : ζ = 1
  · subst h1; simp
  have hord : orderOf ζ = l := orderOf_eq_prime hζ h1
  have hprim : IsPrimitiveRoot ζ l := hord ▸ IsPrimitiveRoot.orderOf ζ
  have hsζ : (s ζ) ^ l = 1 := by rw [← map_pow, hζ, map_one]
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  obtain ⟨k, hk, hk'⟩ := hprim.eq_pow_of_pow_eq_one hsζ
  have hkl : ¬ l ∣ k := by
    rintro ⟨j, rfl⟩
    apply h1
    have : s ζ = 1 := by rw [← hk', pow_mul, hζ, one_pow]
    exact (map_eq_one_iff s s.injective).mp this
  rw [pow_apply_of_apply s ζ k hk'.symm]
  have hz : ((k : ZMod l)) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hf : ((k ^ (l - 1) : ℕ) : ZMod l) = ((1 : ℕ) : ZMod l) := by
    push_cast; exact ZMod.pow_card_sub_one_eq_one hz
  rw [ZMod.natCast_eq_natCast_iff] at hf
  rw [← pow_mod_orderOf, hord, hf, Nat.one_mod_eq_one.mpr hl.out.one_lt.ne', pow_one]

theorem charPow_sub_one_eq_one : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] (C : Type) [Monoid C]
    (χ : G ℚ Ω →* C) (s : G ℚ Ω), KillsMu l χ → χ s ^ (l - 1) = 1 := by
  intro Ω _ _ l _ C _ χ s h
  rw [← map_pow]
  exact h _ fun ζ hζ => pow_fixes l s ζ hζ

end GlobalTheory.KillsMuOrd
