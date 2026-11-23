import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem rco_mul_rco : ∀ k n m j : ℕ, j ≤ m → m ≤ n →
    rco k n m * rco k m j = rco k n j * ((n - j).choose (m - j) : ℤ) := by
  intro k n m j hjm hmn
  have h1 : n.choose m * m.choose j = n.choose j * (n - j).choose (m - j) := by
    first
      | exact Nat.choose_mul hjm
      | exact Nat.choose_mul hmn hjm
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hjm
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have e1 : j + p + q - (j + p) = q := by omega
  have e2 : j + p - j = p := by omega
  have e3 : j + p + q - j = p + q := by omega
  have h2 : ∀ a p q : ℕ, a.ascFactorial p * (a + p).ascFactorial q = a.ascFactorial (p + q) := by
    intro a p q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [← add_assoc, Nat.ascFactorial_succ, Nat.ascFactorial_succ, ← ih, add_assoc a p q]
      ring
  have h3 := h2 (k + j) p q
  rw [e2, e3] at h1
  have h1' : ((j + p + q).choose (j + p) : ℤ) * ((j + p).choose j : ℤ)
      = ((j + p + q).choose j : ℤ) * ((p + q).choose p : ℤ) := by exact_mod_cast h1
  have h3' : ((k + j).ascFactorial p : ℤ) * ((k + (j + p)).ascFactorial q : ℤ)
      = ((k + j).ascFactorial (p + q) : ℤ) := by
    rw [← add_assoc]; exact_mod_cast h3
  unfold rco
  rw [e1, e2, e3, pow_add, ← h3']
  linear_combination ((-1 : ℤ) ^ p * (-1) ^ q * ((k + j).ascFactorial p : ℤ)
    * ((k + (j + p)).ascFactorial q : ℤ)) * h1'

end GlobalTheory.HilbFam
