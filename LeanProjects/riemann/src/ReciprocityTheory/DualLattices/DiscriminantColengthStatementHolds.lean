import ReciprocityTheory.DualLattices.ColengthSqBlockVandermonde
import ReciprocityTheory.DualLattices.ValuationPairwiseDifferenceProductPowLeColengthS
import ReciprocityTheory.DualLattices.ColengthSqMulLe

namespace ReciprocityTheory.PGsh.Up

theorem discriminantColengthStatement_holds : DiscriminantColengthStatement := by
  intro C _ _ v R _ _ _ _ n a hinj ha
  exact ⟨fun s F S hF hS => colength_sq_blockVandermonde a s F S hF hS,
    fun s M S Mτ hM hτ hS => valuation_pairwiseDifferenceProduct_pow_le_colength_sq C v n a s M S Mτ hM hτ hS,
    fun s h A F M' S Mτ hF _ hM' hτ hS => colength_sq_mul_le a hinj ha s h A F M' S Mτ hF hM' hτ hS⟩

end ReciprocityTheory.PGsh.Up
