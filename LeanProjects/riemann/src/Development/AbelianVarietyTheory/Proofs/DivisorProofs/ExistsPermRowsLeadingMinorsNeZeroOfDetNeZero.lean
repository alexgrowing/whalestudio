import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula

namespace GlobalTheory

theorem exists_perm_rows_leading_minors_ne_zero_of_det_ne_zero (K : Type) [Field K] :
    ∀ (N : ℕ) (A : Matrix (Fin N) (Fin N) K), A.det ≠ 0 →
      ∃ w : Equiv.Perm (Fin N), ∀ (k : ℕ) (hk : k ≤ N),
        ((A.submatrix w id).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0 := by
  intro N
  induction N with
  | zero =>
    intro A _
    refine ⟨1, fun k hk => ?_⟩
    obtain rfl : k = 0 := by omega
    simp
  | succ n ih =>
    intro A hA
    have h1 : ∃ i : Fin (n + 1),
        (A.submatrix i.succAbove (Fin.last n).succAbove).det ≠ 0 := by
      by_contra h
      push_neg at h
      apply hA
      rw [Matrix.det_succ_column A (Fin.last n)]
      simp only [h, mul_zero, Finset.sum_const_zero]
    obtain ⟨i, hi⟩ := h1
    obtain ⟨w', hw'⟩ := ih _ hi
    let w : Equiv.Perm (Fin (n + 1)) :=
      (finSuccEquiv' (Fin.last n)).trans ((Equiv.optionCongr w').trans (finSuccEquiv' i).symm)
    have hw : ∀ j : Fin n, w ((Fin.last n).succAbove j) = i.succAbove (w' j) := by
      intro j
      simp only [w, Equiv.trans_apply, finSuccEquiv'_succAbove, Equiv.optionCongr_apply,
        Option.map_some, finSuccEquiv'_symm_some]
    refine ⟨w, fun k hk => ?_⟩
    rcases Nat.lt_or_ge n k with hlt | hle
    · obtain rfl : k = n + 1 := by omega
      have : (Fin.castLE hk : Fin (n + 1) → Fin (n + 1)) = id := by
        funext x; simp
      rw [this, Matrix.submatrix_id_id, Matrix.det_permute]
      refine mul_ne_zero ?_ hA
      rcases Int.units_eq_one_or (Equiv.Perm.sign w) with h | h <;> simp [h]
    · have hc : ∀ x : Fin k, (Fin.castLE hk x : Fin (n + 1))
          = (Fin.last n).succAbove (Fin.castLE hle x) := by
        intro x
        rw [Fin.succAbove_last]
        rfl
      convert hw' k hle using 2
      ext a b
      simp only [Matrix.submatrix_apply, id, hc, hw]

theorem GL_exists_perm_rows_leading_minors_ne_zero :
    ∀ (K : Type) [Field K] (N : ℕ) (g : GL (Fin N) K), ∃ w : Equiv.Perm (Fin N),
      ∀ (k : ℕ) (hk : k ≤ N),
        ((g.1.submatrix w id).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0 := by
  intro K _ N g
  exact exists_perm_rows_leading_minors_ne_zero_of_det_ne_zero K N g.1
    (Matrix.GeneralLinearGroup.det_ne_zero g)

end GlobalTheory
