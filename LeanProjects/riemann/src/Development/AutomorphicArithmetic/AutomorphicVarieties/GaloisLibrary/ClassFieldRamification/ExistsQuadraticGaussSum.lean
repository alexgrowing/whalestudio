import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.Basic

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

private theorem UpperTheory.V.CF.exists_quadratic_gauss_sum {K : Type} [Field K] [CharZero K] {d : ℕ} [hd : Fact d.Prime]
    (hd2 : d ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ d) :
    ∃ G : K, G ^ 2 = (pStar d : ℤ) ∧ G ∈ ℚ⟮ζ⟯ ∧ ∀ (σ : K →+* K) (a : ℕ), σ ζ = ζ ^ a →
      σ G = (legendreSym d a : ℤ) * G := by
  classical
  haveI : NeZero d := ⟨hd.out.ne_zero⟩
  have hζd : ζ ^ d = 1 := hζ.pow_eq_one
  let χ : MulChar (ZMod d) K := (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom K)
  let ψ : AddChar (ZMod d) K := AddChar.zmodChar d hζd
  have hψp : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root d hζ
  have hchar : ringChar (ZMod d) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hd2
  have hχ1 : χ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (f := Int.castRingHom K) Int.cast_injective).2
      (quadraticChar_ne_one hchar)
  have hχq : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod d)).comp _
  have hχa : ∀ a : ZMod d, χ a = ((quadraticChar (ZMod d) a : ℤ) : K) := fun a => by
    simp [χ, MulChar.ringHomComp_apply]
  have hψa : ∀ n : ℕ, ψ (n : ZMod d) = ζ ^ n := fun n => AddChar.zmodChar_apply' hζd n
  refine ⟨gaussSum χ ψ, ?_, ?_, ?_⟩
  · rw [gaussSum_sq hχ1 hχq hψp, hχa, ZMod.card]
    have h1 : quadraticChar (ZMod d) (-1) = legendreSym d (-1) := by
      simp [legendreSym]
    rw [h1, legendreSym.at_neg_one hd2, ZMod.χ₄_nat_eq_if_mod_four, pStar]
    have hodd : d % 2 = 1 := hd.out.eq_two_or_odd.resolve_left hd2
    have h4 : d % 4 = 1 ∨ d % 4 = 3 := by omega
    rcases h4 with h4 | h4
    · have he : Even (d / 2) := by rw [Nat.even_iff]; omega
      simp [hodd, h4, he.neg_one_pow]
    · have ho : Odd (d / 2) := by rw [Nat.odd_iff]; omega
      simp [hodd, h4, ho.neg_one_pow]
  · unfold gaussSum
    refine IntermediateField.sum_mem _ fun a _ => IntermediateField.mul_mem _ ?_ ?_
    · rw [hχa]; exact IntermediateField.intCast_mem _ _
    · rw [← ZMod.natCast_zmod_val a, hψa]
      exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ ζ) _
  · intro σ b hσ
    have hG : σ (gaussSum χ ψ) = gaussSum χ (ψ.mulShift (b : ZMod d)) := by
      unfold gaussSum
      rw [map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, hχa, map_intCast, AddChar.mulShift_apply]
      congr 1
      rw [← ZMod.natCast_zmod_val a, hψa, map_pow, hσ, ← pow_mul, ← Nat.cast_mul, hψa]
    have hb : (b : ZMod d) ≠ 0 := by
      intro h0
      have h1 : σ ζ = 1 := by
        rw [hσ]
        rw [ZMod.natCast_eq_zero_iff] at h0
        obtain ⟨k, rfl⟩ := h0
        rw [pow_mul, hζd, one_pow]
      have h2 : ζ = 1 := σ.injective (by rw [h1, map_one])
      exact hζ.ne_one hd.out.one_lt h2
    have hmul : χ (b : ZMod d) * gaussSum χ (ψ.mulShift (b : ZMod d)) = gaussSum χ ψ :=
      gaussSum_mulShift χ ψ (Units.mk0 _ hb)
    have hu2 : χ (b : ZMod d) * χ (b : ZMod d) = 1 := by
      rw [hχa, ← Int.cast_mul, ← sq, quadraticChar_sq_one hb, Int.cast_one]
    have hleg : ((legendreSym d b : ℤ) : K) = χ (b : ZMod d) := by
      rw [hχa]; simp [legendreSym]
    rw [hG, hleg, ← hmul, ← mul_assoc, hu2, one_mul]

theorem UpperTheory.V.CF.gauss :
    ∀ (K : Type) [Field K] [CharZero K] (p : ℕ) [Fact p.Prime] (ζ : K), p ≠ 2 → IsPrimitiveRoot ζ p → (∃ x : K, x ^ 2 = (pStar p : ℤ)) ∧ ∀ x : K, x ^ 2 = (pStar p : ℤ) → x ∈ ℚ⟮ζ⟯ ∧ ∀ (σ : K →+* K) (b : ℕ), σ ζ = ζ ^ b → σ x = (legendreSym p b : ℤ) * x := by
  intro K _ _ p _ ζ hp hζ
  obtain ⟨G, hG, hmem, hσ⟩ := UpperTheory.V.CF.exists_quadratic_gauss_sum hp hζ
  refine ⟨⟨G, hG⟩, fun x hx => ?_⟩
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hx.trans hG.symm) with rfl | rfl
  · exact ⟨hmem, hσ⟩
  · refine ⟨neg_mem hmem, fun σ b h => ?_⟩
    rw [map_neg, hσ σ b h, mul_neg]
