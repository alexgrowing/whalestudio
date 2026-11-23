import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockWordOfTypeProd
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_block_word_of_type_prod : ∀ (D t : ℕ) (α : Fin D →₀ ℕ), α.degree ≤ t → ∃ β : Fin t → Fin (D + 1), (∀ i : Fin D, (Finset.univ.filter fun q => β q = i.castSucc).card = α i) ∧ (α.degree = t → ∀ q, β q ≠ Fin.last D) ∧ ∀ (M : Type) [Monoid M] (f : Fin (D + 1) → M), (List.ofFn fun q => f (β q)).prod = (List.ofFn fun i : Fin D => f i.castSucc ^ α i).prod * f (Fin.last D) ^ (t - α.degree) := by
  first | exact @GlobalTheory.HSShort.words_of_type | exact GlobalTheory.HSShort.words_of_type | (intros; apply GlobalTheory.HSShort.words_of_type <;> assumption)
