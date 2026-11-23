import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem clear_denominators : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε)
    (P : Polynomial T.K), P ≠ 0 → ∃ (p : ℕ → GlobalTheory.FN.ring ε.range) (u : T.K), u ≠ 0 ∧ p P.natDegree ≠ 0 ∧
      ∀ i, T.io (p i) = u * P.coeff i := by
  intro Ω _ _ _ ε T P hP
  classical
  choose a b hb hab using T.io_surj
  set S := Finset.range (P.natDegree + 1) with hS
  have hbne : ∀ f, T.io (b f) ≠ 0 := fun f h => hb f (T.io_inj (by rw [h, map_zero]))
  refine ⟨fun i => if i ∈ S then a (P.coeff i) * ∏ j ∈ S.erase i, b (P.coeff j) else 0,
    T.io (∏ j ∈ S, b (P.coeff j)), ?_, ?_, ?_⟩
  · rw [map_prod]; exact Finset.prod_ne_zero_iff.mpr fun j _ => hbne _
  · have hmem : P.natDegree ∈ S := by simp [hS]
    intro h
    simp only [hmem, if_true] at h
    have h2 := congrArg T.io h
    rw [map_zero, map_mul, ← hab, map_prod, mul_assoc, Finset.mul_prod_erase S (fun j => T.io (b (P.coeff j))) hmem] at h2
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact hP (Polynomial.leadingCoeff_eq_zero.mp h3)
    · exact (Finset.prod_ne_zero_iff.mpr fun j _ => hbne _) h3
  · intro i
    by_cases hi : i ∈ S
    · simp only [hi, if_true]
      rw [map_mul, ← hab, map_prod, map_prod, mul_assoc, Finset.mul_prod_erase S (fun j => T.io (b (P.coeff j))) hi, mul_comm]
    · simp only [hi, if_false, map_zero]
      have : P.natDegree < i := by simp [hS] at hi; omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt this, mul_zero]

end GlobalTheory.FN
