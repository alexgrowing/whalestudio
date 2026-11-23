import Formalism.PadicSubsetSums.CentralIdempotents.ArchimedeanComponents
import Formalism.PadicSubsetSums.StableGradedCounts.ARCReuse

namespace Formalism.IrreducibleCountingLemmas.WindowSums

open Polynomial

theorem sqrt_neg_in_cyclotomic_field : SqrtNegInCyclotomic := by
  intro l hl h4 F _ ζ hζ
  have := Fact.mk hl
  by_cases h2 : (2 : F) = 0
  · have h1 : (l : F) = 1 := by
      obtain ⟨k, hk⟩ : ∃ k, l = 2 * k + 1 := ⟨l / 2, by omega⟩
      rw [hk]; push_cast; rw [h2]; ring
    have hneg : (-1 : F) = 1 := by linear_combination -h2
    rw [h1, hneg]; exact IsSquare.one
  · have hchar : ringChar (ZMod l) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
    have hm1 : quadraticChar (ZMod l) (-1) = -1 := by
      rw [quadraticChar_neg_one hchar, ZMod.card, ZMod.χ₄_nat_three_mod_four h4]
    have hχm1 : ((quadraticChar (ZMod l)).ringHomComp (Int.castRingHom F)) (-1) = -1 := by
      simp [MulChar.ringHomComp_apply, hm1]
    have hχ1 : (quadraticChar (ZMod l)).ringHomComp (Int.castRingHom F) ≠ 1 := by
      intro h
      rw [h, MulChar.one_apply (isUnit_one.neg)] at hχm1
      apply h2; linear_combination hχm1
    have hq : ((quadraticChar (ZMod l)).ringHomComp (Int.castRingHom F)).IsQuadratic :=
      (quadraticChar_isQuadratic (ZMod l)).comp _
    have hψ := AddChar.zmodChar_primitive_of_primitive_root l hζ
    have hsq := gaussSum_sq hχ1 hq hψ
    rw [hχm1, ZMod.card] at hsq
    exact ⟨gaussSum _ _, by rw [← sq, hsq]; ring⟩

end Formalism.IrreducibleCountingLemmas.WindowSums
