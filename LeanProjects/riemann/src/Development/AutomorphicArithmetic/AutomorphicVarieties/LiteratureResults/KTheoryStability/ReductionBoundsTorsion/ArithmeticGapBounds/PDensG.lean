import Mathlib

namespace PositivityTheory.KB.SpectralGap.WordTransvectionCongruences

open Matrix

theorem diagonal_decomposition_transvections {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] {i j : ι} (hij : i ≠ j)
    {a : F} (ha : a ≠ 0) :
    SpecialLinearGroup.diag2n hij a ha = SpecialLinearGroup.transvection hij a *
      SpecialLinearGroup.transvection hij.symm (-a⁻¹) * SpecialLinearGroup.transvection hij a *
      SpecialLinearGroup.transvection hij (-1) * SpecialLinearGroup.transvection hij.symm 1 *
      SpecialLinearGroup.transvection hij (-1) := by
  apply SpecialLinearGroup.coeMonoidHom_injective
  simp only [map_mul, SpecialLinearGroup.coeMonoidHom_apply, SpecialLinearGroup.diag2n_coe, SpecialLinearGroup.transvection_coe, mul_add, add_mul,
    one_mul, mul_one, single_mul_single_same]
  simp only [single_mul_single_of_ne _ _ _ _ hij.symm, single_mul_single_of_ne _ _ _ _ hij,
    zero_add, add_zero, single_mul_single_same, zero_mul, mul_zero]
  ext x y
  by_cases hxi : i = x
  · subst x
    by_cases hyi : i = y
    · subst y; (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))
    by_cases hyj : j = y
    · subst y; (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))
    (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))
  by_cases hxj : j = x
  · subst x
    by_cases hyi : i = y
    · subst y; (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))
    by_cases hyj : j = y
    · subst y; (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))
    (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))
  by_cases hyi : i = y
  · subst y; (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))
  by_cases hyj : j = y
  · subst y; (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))
  (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))

theorem sl_top {ι F : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι] [Field F]
    (S : Subgroup (SpecialLinearGroup ι F))
    (h : ∀ (i j : ι) (hij : i ≠ j) (c : F), SpecialLinearGroup.transvection hij c ∈ S) : S = ⊤ := by
  have hdiag : ∀ (i j : ι) (hij : i ≠ j) {c : F} (hc : c ≠ 0),
      SpecialLinearGroup.diag2n hij c hc ∈ S := by
    intro i j hij c hc
    rw [diagonal_decomposition_transvections hij hc]
    exact S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (h _ _ _ _) (h _ _ _ _))
      (h _ _ _ _)) (h _ _ _ _)) (h _ _ _ _)) (h _ _ _ _)
  refine eq_top_iff.2 fun M _ => ?_
  exact SpecialLinearGroup.diagonal_transvection_induction' (· ∈ S) M hdiag h
    (fun _ _ => S.mul_mem)

end PositivityTheory.KB.SpectralGap.WordTransvectionCongruences
