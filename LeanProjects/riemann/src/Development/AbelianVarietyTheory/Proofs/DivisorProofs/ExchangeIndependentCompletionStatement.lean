import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExchangeIndependentCompletion
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_independent_completion : ∀ (E M : Type) [Field E] [AddCommGroup M] [Module E M] (n d : ℕ) (v : Fin n → M) (w : Fin d → M), LinearIndependent E v → LinearIndependent E w → (∀ k, v k ∈ Submodule.span E (Set.range w)) → ∃ K : Finset (Fin d), n + K.card = d ∧ LinearIndependent E (Sum.elim v fun k : K => w k) := by
  first | exact @GlobalTheory.exchange_independent_completion | exact GlobalTheory.exchange_independent_completion | (intros; apply GlobalTheory.exchange_independent_completion <;> assumption)
