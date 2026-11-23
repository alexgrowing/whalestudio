import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockLuDecompositionExists
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_lu_decomposition_exists : ∀ (A : Type) [CommRing A] (N : ℕ) (S : Set ℕ) (g : GL (Fin N) A), (∀ (k : ℕ) (hk : k ≤ N), IsUnit (g.1.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) → ∃ L b : GL (Fin N) A, g = L * b ∧ (∀ i j : Fin N, ¬ (∃ s ∈ S, (j : ℕ) < s ∧ s ≤ (i : ℕ)) → L.1 i j = (1 : Matrix (Fin N) (Fin N) A) i j) ∧ ∀ i j : Fin N, (∃ s ∈ S, (j : ℕ) < s ∧ s ≤ (i : ℕ)) → b.1 i j = 0 := by
  first | exact @GlobalTheory.exists_blockLower_mul_blockUpper | exact GlobalTheory.exists_blockLower_mul_blockUpper | (intros; apply GlobalTheory.exists_blockLower_mul_blockUpper <;> assumption)
