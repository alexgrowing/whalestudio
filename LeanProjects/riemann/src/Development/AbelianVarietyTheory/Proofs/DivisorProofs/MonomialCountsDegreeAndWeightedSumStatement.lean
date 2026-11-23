import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialCountsDegreeAndWeightedSum
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomial_counts_degree_and_weighted_sum : ∀ D T : ℕ, 1 ≤ D → D + 1 ≤ T → (∀ a : ℕ, Nat.card (MonoDeg (Fin D) a) = (a + D - 1).choose (D - 1)) ∧ Nat.card (Σ a : Fin (T - D), MonoDeg (Fin D) a) = (T - 1).choose D ∧ (D + 1) * ∑ a ∈ Finset.range (T - D), (a + D - 1).choose (D - 1) * (T - a) = (T - 1).choose D * (T + D * (D + 1)) := by
  first | exact @GlobalTheory.HSShort.monomial_counts | exact GlobalTheory.HSShort.monomial_counts | (intros; apply GlobalTheory.HSShort.monomial_counts <;> assumption)
