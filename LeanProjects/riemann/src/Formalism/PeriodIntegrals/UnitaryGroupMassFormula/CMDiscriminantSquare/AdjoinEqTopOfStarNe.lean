import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMDiscriminantSquare.RelDiffTop

open NumberField Polynomial

namespace PIW.CMDiscSq

theorem exists_of_star_eq {F E : Type} [Field F] [Field E] [StarRing E] [Algebra F E]
    (hR : Set.range (algebraMap F E) = {a : E | star a = a}) {y : E} (hy : star y = y) :
    ∃ a : F, algebraMap F E a = y := by
  have : y ∈ Set.range (algebraMap F E) := by rw [hR]; exact hy
  exact this

theorem adjoin_eq_top_of_star_ne {F E : Type} [Field F] [Field E] [StarRing E] [Algebra F E]
    (hR : Set.range (algebraMap F E) = {a : E | star a = a}) {x : E} (hx : star x ≠ x) :
    Algebra.adjoin F {x} = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hd : x - star x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hbd : (y - star y) / (x - star x) * (x - star x) = y - star y := div_mul_cancel₀ _ hd
  have hb : star ((y - star y) / (x - star x)) = (y - star y) / (x - star x) := by
    rw [star_div₀, star_sub, star_sub, star_star, star_star, ← neg_sub y, ← neg_sub x,
      neg_div_neg_eq]
  have ha : star (y - (y - star y) / (x - star x) * x) = y - (y - star y) / (x - star x) * x := by
    rw [star_sub, star_mul', hb]
    linear_combination hbd
  obtain ⟨b, hb'⟩ := exists_of_star_eq hR hb
  obtain ⟨a, ha'⟩ := exists_of_star_eq hR ha
  have hy : y = algebraMap F E a + algebraMap F E b * x := by rw [ha', hb']; ring
  rw [hy]
  exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ a)
    (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ b) (Algebra.subset_adjoin rfl))

theorem minpoly_eq_of_star_ne {F E : Type} [Field F] [Field E] [StarRing E] [Algebra F E]
    [FiniteDimensional F E]
    (hR : Set.range (algebraMap F E) = {a : E | star a = a}) {x : E} (hx : star x ≠ x) :
    ∃ s n : F, algebraMap F E s = x + star x ∧ algebraMap F E n = x * star x ∧
      minpoly F x = X ^ 2 - C s * X + C n := by
  obtain ⟨s, hs⟩ := exists_of_star_eq hR (y := x + star x) (by rw [star_add, star_star, add_comm])
  obtain ⟨n, hn⟩ := exists_of_star_eq hR (y := x * star x) (by rw [star_mul', star_star, mul_comm])
  refine ⟨s, n, hs, hn, ?_⟩
  have hmon : (X ^ 2 - C s * X + C n : F[X]).Monic := by monicity!
  have hdeg : (X ^ 2 - C s * X + C n : F[X]).natDegree = 2 := by compute_degree!
  have hroot : aeval x (X ^ 2 - C s * X + C n : F[X]) = 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, hs, hn]
    ring
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have h2 : 2 ≤ (minpoly F x).natDegree := by
    rw [minpoly.two_le_natDegree_iff hint]
    rintro ⟨a, rfl⟩
    apply hx
    have : algebraMap F E a ∈ Set.range (algebraMap F E) := ⟨a, rfl⟩
    rw [hR] at this
    exact this
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmon
    (minpoly.dvd F x hroot) (by rw [hdeg]; exact h2)).symm

end PIW.CMDiscSq
