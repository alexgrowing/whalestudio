import Development.AutomorphicArithmetic.QuadraticCharacters.FieldOf
import Development.AutomorphicArithmetic.QuadraticCharacters.A0InfStabilizerTrivial

open NumberField IntermediateField

namespace HostParam

namespace SlopeTestRemainingChoices.GaussRoot

theorem exists_gauss {K : Type} [Field K] [CharZero K] {d : ℕ} [hd : Fact d.Prime]
    (hd4 : d % 4 = 3) {ζ : K} (hζ : IsPrimitiveRoot ζ d) :
    ∃ G : K, G ^ 2 = -(d : K) ∧ ∀ (σ : K →+* K) (a : ℕ), a.Coprime d → σ ζ = ζ ^ a →
      σ G = ((quadraticChar (ZMod d) (a : ZMod d) : ℤ) : K) * G := by
  haveI : NeZero d := ⟨hd.out.ne_zero⟩
  have hζ1 : ζ ^ d = 1 := hζ.pow_eq_one
  let χ : MulChar (ZMod d) K := (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom K)
  let ψ : AddChar (ZMod d) K := AddChar.zmodChar d hζ1
  have hchar : ringChar (ZMod d) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  have hχ1 : χ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff Int.cast_injective).mpr (quadraticChar_ne_one hchar)
  have hχq : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod d)).comp _
  have hψ : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root d hζ
  refine ⟨gaussSum χ ψ, ?_, ?_⟩
  · rw [gaussSum_sq hχ1 hχq hψ, ZMod.card]
    have hm : χ (-1) = -1 := by
      simp only [χ, MulChar.ringHomComp_apply, quadraticChar_neg_one hchar, ZMod.card,
        ZMod.χ₄_nat_three_mod_four hd4]
      simp
    rw [hm]
    ring
  · intro σ a ha hσ
    have hσψ : ∀ x : ZMod d, σ (ψ x) = ψ (a * x) := by
      intro x
      calc σ (ψ x) = σ (ζ ^ x.val) := rfl
        _ = ζ ^ (a * x.val) := by rw [map_pow, hσ, ← pow_mul]
        _ = ψ ((a * x.val : ℕ) : ZMod d) := (AddChar.zmodChar_apply' hζ1 _).symm
        _ = ψ (a * x) := by
          push_cast
          rw [ZMod.natCast_zmod_val]
    let u : (ZMod d)ˣ := ZMod.unitOfCoprime a ha
    have hG : σ (gaussSum χ ψ) = gaussSum χ (ψ.mulShift u) := by
      simp only [gaussSum, map_sum, map_mul, AddChar.mulShift_apply]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [hσψ]
      simp [χ, u]
    rw [hG, gaussSum_mulShift_eq, hχq.inv]
    simp [χ, u]

theorem eq_or_neg {K : Type} [Field K] {a b c : K} (ha : a ^ 2 = c) (hb : b ^ 2 = c) :
    a = b ∨ a = -b := sq_eq_sq_iff_eq_or_eq_neg.mp (ha.trans hb.symm)

theorem ne_zero {K : Type} [Field K] [CharZero K] {d : ℕ} (hd : d.Prime) {b : K}
    (hb : b ^ 2 = -(d : K)) : b ≠ 0 := by
  rintro rfl
  have : (d : K) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne_zero
  apply this
  rw [← neg_eq_zero, ← hb]
  simp

end SlopeTestRemainingChoices.GaussRoot

namespace AbField
variable (E : AbField)

end AbField

end HostParam
