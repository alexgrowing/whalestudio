import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMDiscriminantSquare.RelDiffTop

open NumberField Module

noncomputable section

namespace PIW.CMDiscSq

theorem exists_star_ne {E : Type} [Field E] [NumberField E] [StarRing E]
    (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) : ∃ x : E, star x ≠ x := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 E)
  obtain ⟨θ, t, ht, hθ⟩ := hE.2.2 P hP
  refine ⟨algebraMap (𝓞 E) E θ, ?_⟩
  rw [← ht]
  intro h
  apply hθ
  have : t = θ := RingOfIntegers.coe_injective h
  rw [this, sub_self]
  exact P.zero_mem

theorem finrank_two_of {F E : Type} [Field F] [Field E] [StarRing E] [Algebra F E]
    (hR : Set.range (algebraMap F E) = {a : E | star a = a}) (x : E) (hx : star x ≠ x) :
    finrank F E = 2 := by
  have hmem : ∀ a : E, star a = a → ∃ c : F, algebraMap F E c = a := by
    intro a ha
    have : a ∈ Set.range (algebraMap F E) := by rw [hR]; exact ha
    exact this
  have hfix : ∀ c : F, star (algebraMap F E c) = algebraMap F E c := by
    intro c
    have : algebraMap F E c ∈ Set.range (algebraMap F E) := ⟨c, rfl⟩
    rw [hR] at this
    exact this
  have hd : x - star x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  let v : Fin 2 → E := ![1, x]
  have hli : LinearIndependent F v := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    by_cases ht : t = 0
    · subst ht
      simp only [map_zero, zero_mul, add_zero] at hst
      exact ⟨(FaithfulSMul.algebraMap_injective F E) (by rw [hst, map_zero]), rfl⟩
    · exfalso
      have htE : algebraMap F E t ≠ 0 := by
        intro h0
        apply ht
        exact (FaithfulSMul.algebraMap_injective F E) (by rw [h0, map_zero])
      have hxe : x = algebraMap F E (-s / t) := by
        rw [map_div₀, map_neg]
        field_simp
        linear_combination hst
      apply hx
      rw [hxe, hfix]
  have hsp : ⊤ ≤ Submodule.span F (Set.range v) := by
    intro y _
    have hb : star ((y - star y) / (x - star x)) = (y - star y) / (x - star x) := by
      rw [star_div₀, star_sub, star_sub, star_star, star_star]
      rw [← neg_sub y, ← neg_sub x, neg_div_neg_eq]
    obtain ⟨b, hb'⟩ := hmem _ hb
    have ha : star (y - algebraMap F E b * x) = y - algebraMap F E b * x := by
      rw [star_sub, star_mul', hfix, hb']
      field_simp
      ring
    obtain ⟨a, ha'⟩ := hmem _ ha
    have hy : y = a • v 0 + b • v 1 := by
      simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.smul_def, mul_one]
      rw [ha']
      ring
    rw [hy]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have bas := Basis.mk hli hsp
  rw [finrank_eq_card_basis bas, Fintype.card_fin]

theorem relDegTwo : RelDegTwo := by
  intro F E _ _ _ _ _ _ hFE
  obtain ⟨x, hx⟩ := exists_star_ne hFE.1
  exact finrank_two_of hFE.2 x hx

end PIW.CMDiscSq
