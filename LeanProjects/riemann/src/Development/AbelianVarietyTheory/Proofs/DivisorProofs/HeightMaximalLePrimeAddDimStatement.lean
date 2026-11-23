import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightMaximalLePrimeAddDim
import Mathlib
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.PolyCM
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_maximal_le_prime_add_dim : ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A] (P M : Ideal A) [P.IsPrime] [M.IsMaximal], (M.height : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) + ringKrullDim (A ⧸ P) := by
  first | exact @GlobalTheory.FinTypeIntCatenary.height_maximal_le | exact GlobalTheory.FinTypeIntCatenary.height_maximal_le | (intros; apply GlobalTheory.FinTypeIntCatenary.height_maximal_le <;> assumption)
