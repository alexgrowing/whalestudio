import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RamifiedPrimeLossLeValuationPrimePower
import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramified_prime_loss_le_valuation_prime_power : ∀ (D : D7) (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (j : ℕ) (w : WeightFamilies.Wt D j) (a b : ℕ), c2 D w ≤ a → Formalism.MainNotions.DIV.Cons.cHalf w ≤ b → ramLoss D la w ≤ ((vLa la ((pPow D a b b : ℕ) : K) : ℤ) : ℝ) := by
  first | exact @GlobalTheory.PlaceTop.ramLoss_le_vLa_pPow | exact GlobalTheory.PlaceTop.ramLoss_le_vLa_pPow | (intros; apply GlobalTheory.PlaceTop.ramLoss_le_vLa_pPow <;> assumption)
