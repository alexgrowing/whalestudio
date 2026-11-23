import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntWeightsCompatibleRootsOfUnityLevels
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_int_weights_compatibleRootsOfUnity_levels : ∀ (l : ℕ) [Fact l.Prime] (ζ : ℕ → Om l), ζ 0 = 1 → ζ 1 ≠ 1 → (∀ j, ζ (j + 1) ^ l = ζ j) → ∀ s j n : ℕ, 1 ≤ j → j ≤ s → ¬ l ∣ n → ∃ lam : ℕ → ℤ, (∑ a ∈ primeTo l s, lam a = if j = 1 then (l : ℤ) ^ (s - 1) else 0) ∧ ∀ i, 1 ≤ i → i ≤ s → ∑ a ∈ primeTo l s, (lam a : Om l) * ζ i ^ a = if i = j then (l : Om l) ^ (if j = 1 then s - 1 else s - j + 1) * ζ j ^ n else 0 := by
  first | exact @GlobalTheory.LevelSums.exists_weights | exact GlobalTheory.LevelSums.exists_weights | (intros; apply GlobalTheory.LevelSums.exists_weights <;> assumption)
