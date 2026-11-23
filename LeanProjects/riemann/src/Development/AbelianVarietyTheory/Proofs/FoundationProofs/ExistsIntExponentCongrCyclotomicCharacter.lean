import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem exists_int_exponent_cyclotomic {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (l : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) (n M : ℕ) (hM : 0 < M) (hd : l ^ n ∣ M) :
    ∃ e : ℤ, (∀ ζ : Ω, IsPrimitiveRoot ζ M → s ζ = ζ ^ e) ∧
      (e : ℤ_[l]) - (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) ∈ (idl l) ^ n := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := algebraRat.charZero Ω
  have : NeZero M := ⟨hM.ne'⟩
  have : NeZero (M : Ω) := ⟨Nat.cast_ne_zero.mpr hM.ne'⟩
  have : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨e, he⟩ := rootsOfUnity.integer_power_of_ringEquiv M s.toRingEquiv
  have hs : ∀ ζ : Ω, IsPrimitiveRoot ζ M → s ζ = ζ ^ e := by
    intro ζ hζ
    have h := he hζ.toRootsOfUnity
    simpa [Units.val_zpow_eq_zpow_val] using h
  refine ⟨e, hs, ?_⟩
  obtain ⟨k, hk⟩ := hd
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have hη : IsPrimitiveRoot (ζ ^ k) (l ^ n) := hζ.pow hM (by rw [hk, mul_comm])
  have hsη : s (ζ ^ k) = (ζ ^ k) ^ e := by
    rw [map_pow, hs ζ hζ, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
  set c := (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) with hc
  have hpow : (ζ ^ k) ^ (l ^ n) = 1 := hη.pow_eq_one
  have hspec := cyclotomicCharacter.spec (L := Ω) l s.toRingEquiv (ζ ^ k) hpow
  have heq : (ζ ^ k) ^ e = (ζ ^ k) ^ (((cyclotomicCharacter Ω l s.toRingEquiv).val.toZModPow n).val : ℤ) := by
    rw [← hsη, zpow_natCast]
    exact hspec
  have hdvd : ((l ^ n : ℕ) : ℤ) ∣ e - (((cyclotomicCharacter Ω l s.toRingEquiv).val.toZModPow n).val : ℤ) := by
    rw [← hη.zpow_eq_one_iff_dvd, zpow_sub₀ (hη.ne_zero (NeZero.ne _)), heq, div_self]
    exact zpow_ne_zero _ (pow_ne_zero _ (hζ.ne_zero (NeZero.ne _)))
  have hz : (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)) ((e : ℤ_[l]) - c) = 0 := by
    rw [map_sub, map_intCast, hc]
    rw [sub_eq_zero]
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (l ^ n)).mpr hdvd
    rw [Int.cast_sub, sub_eq_zero] at this
    rw [this]
    simp
  have hmem : (e : ℤ_[l]) - c ∈ RingHom.ker (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)) := hz
  rw [PadicInt.ker_toZModPow, ← Ideal.span_singleton_pow] at hmem
  exact hmem

end GlobalTheory.KZ
