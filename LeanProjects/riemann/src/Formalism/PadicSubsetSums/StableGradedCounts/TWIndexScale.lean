import Formalism.PadicSubsetSums.StableGradedCounts.TWIndexDet

open Module

namespace Formalism.IrreducibleCountingLemmas.TW

theorem index_scaling : IndexScale := by
  intro O K V _ _ _ _ _ _ _ _ _ _ _ M N ϖ u n hM hN hϖ
  have hinj := IsFractionRing.injective O K
  have hc : algebraMap O K ((u : O) * ϖ ^ n) ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 (mul_ne_zero u.ne_zero (pow_ne_zero _ hϖ.ne_zero))
  obtain ⟨d, β, rfl⟩ := Idx.exists_basis hN
  have hd : Module.finrank K V = d := by
    simpa using Module.finrank_eq_card_basis β
  let wb : Basis (Fin d) K V :=
    β.isUnitSMul (w := fun _ => algebraMap O K ((u : O) * ϖ ^ n)) (fun _ => isUnit_iff_ne_zero.2 hc)
  have hspan : scaleLat ((u : O) * ϖ ^ n) (Submodule.span O (Set.range β))
      = Submodule.span O (Set.range wb) := by
    unfold scaleLat
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    ext i
    simp only [Function.comp_apply, LinearMap.lsmul_apply, wb, Basis.isUnitSMul_apply,
      algebraMap_smul]
  have hdet : β.det wb = algebraMap O K ((u ^ d : Oˣ) : O)
      * (algebraMap O K ϖ) ^ ((d : ℤ) * (n : ℤ)) := by
    rw [Basis.det_isUnitSMul, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_mul,
      mul_pow, Units.val_pow_eq_pow_val, map_pow, map_pow, ← pow_mul, mul_comm n d]
    norm_cast
  have h1 := index_of_determinant O K V d β wb ϖ (u ^ d) ((d : ℤ) * (n : ℤ)) hϖ hdet
  have h2 := (index_additive O K V M _ _ hM hN (Idx.isLat_span_basis (O := O) wb)).2
  rw [hspan, hd, ← h2, h1]

end Formalism.IrreducibleCountingLemmas.TW
