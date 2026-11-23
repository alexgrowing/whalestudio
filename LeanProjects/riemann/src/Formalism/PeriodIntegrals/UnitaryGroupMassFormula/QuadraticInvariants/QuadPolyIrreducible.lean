import Mathlib
import Formalism.PeriodIntegrals.ClassNumImQ

open NumberField Polynomial

namespace PI.UnitaryGroupMassFormula.ClassNumImQInv

open PI.ClassNumImQ

variable {d : ℕ} {K : Type} [Field K] [NumberField K] {b : K}

theorem b_ne_rat (hq : QuadData d K b) (r : ℚ) : (r : K) ≠ b := by
  intro h
  obtain ⟨hp, -, -, hb, -⟩ := hq
  rw [← h] at hb
  have h2 : r ^ 2 = -(d : ℚ) := by exact_mod_cast hb
  have hd : (0 : ℚ) < d := by exact_mod_cast hp.pos
  nlinarith [sq_nonneg r]

noncomputable def quadPoly (d : ℕ) : ℚ[X] := X ^ 2 + C (d : ℚ)

theorem quadPoly_monic (d : ℕ) : (quadPoly d).Monic := by
  exact Polynomial.monic_X_pow_add_C _ two_ne_zero

theorem quadPoly_natDegree (d : ℕ) : (quadPoly d).natDegree = 2 := by
  unfold quadPoly
  exact Polynomial.natDegree_X_pow_add_C

theorem aeval_quadPoly (hq : QuadData d K b) : aeval b (quadPoly d) = 0 := by
  obtain ⟨-, -, -, hb, -⟩ := hq
  unfold quadPoly
  simp [hb]

theorem quadPoly_irreducible (hq : QuadData d K b) : Irreducible (quadPoly d) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [quadPoly_natDegree]; simp
  · intro x hx
    obtain ⟨hp, -, -, -, -⟩ := hq
    unfold quadPoly at hx
    simp only [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at hx
    have hd : (0 : ℚ) < d := by exact_mod_cast hp.pos
    nlinarith [sq_nonneg x]

theorem minpoly_b (hq : QuadData d K b) : minpoly ℚ b = quadPoly d := by
  exact (minpoly.eq_of_irreducible_of_monic (quadPoly_irreducible hq) (aeval_quadPoly hq)
    (quadPoly_monic d)).symm

theorem finrank_two (hq : QuadData d K b) : Module.finrank ℚ K = 2 := by
  have hI : IsIntegral ℚ b := IsIntegral.of_finite ℚ b
  rw [← IntermediateField.finrank_top', ← hq.2.2.2.2, IntermediateField.adjoin.finrank hI, minpoly_b hq,
    quadPoly_natDegree]

end PI.UnitaryGroupMassFormula.ClassNumImQInv
