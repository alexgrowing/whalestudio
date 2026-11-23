import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

theorem exists_quaternion_matrix (m : ℕ) : ∃ A : Matrix (Fin 4) (Fin 4) ℤ,
    A.transpose * A = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares m
  have h' : (m : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2 := by
    rw [← h]; push_cast; ring
  refine ⟨!![(a : ℤ), -b, -c, -d; b, a, -d, c; c, d, a, -b; d, -c, b, a], ?_⟩
  rw [h']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, Matrix.one_apply] <;> ring

theorem exists_admissibleKeyNumericalData_prime_to : ∀ g p : ℕ, 1 ≤ g → p.Prime → ∃ (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ), admitted g n l l' al ∧ ¬ p ∣ degProd g n l l' ∧ 1 ≤ degProd g n l l' ∧ 1 ≤ kaExp g n l l' := by
  intro g p hg hp
  choose al hal using exists_quaternion_matrix
  have hp0 := hp.pos
  have hnd : ¬ p ∣ degProd g (4 * p) (g * (4 * p) + 1) (g * (4 * p) + 1 + p) := by
    unfold degProd
    rw [Prime.dvd_finset_prod_iff hp.prime]
    rintro ⟨j, hj, hd⟩
    have hj' : j ≤ g := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj'
    have e1 : (j + k) * (4 * p) + 1 - j * (4 * p) = p * (4 * k) + 1 := by
      apply Nat.sub_eq_of_eq_add; ring
    have e2 : (j + k) * (4 * p) + 1 + p - j * (4 * p) = p * (4 * k + 1) + 1 := by
      apply Nat.sub_eq_of_eq_add; ring
    rw [e1, e2] at hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
    · exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_right _ _)).mp h))
    · exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_right _ _)).mp h))
  have hpos : 0 < degProd g (4 * p) (g * (4 * p) + 1) (g * (4 * p) + 1 + p) :=
    Nat.pos_of_ne_zero fun h => hnd (h ▸ dvd_zero p)
  refine ⟨4 * p, g * (4 * p) + 1, g * (4 * p) + 1 + p, al, ⟨by omega, by omega, by omega, hal⟩,
    hnd, hpos, ?_⟩
  unfold kaExp
  have h1 : 0 < g * (4 * p) + 1 + p - (g * (4 * p) + 1) := by omega
  have h2 := Nat.factorial_pos g
  apply Nat.succ_le_of_lt
  positivity

end GlobalTheory.KeyKa
