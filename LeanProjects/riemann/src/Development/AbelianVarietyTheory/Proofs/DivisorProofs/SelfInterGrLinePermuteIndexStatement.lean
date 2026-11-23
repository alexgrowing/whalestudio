import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfInterGrLinePermuteIndex
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
open GlobalTheory.CovTop GlobalTheory.FlagZ GlobalTheory.ArInt Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfInter_grLine_permute_index : Hypotheses2 → ∀ (ι : Type) [Fintype ι] (N : ℕ) (σ : Equiv.Perm ι) (n : ι × Fin N → ℤ) (a : ℝ), (comb (grLine (ι := ι) (N := N)) n).IsSelfInter a → (comb (grLine (ι := ι) (N := N)) fun x => n (σ x.1, x.2)).IsSelfInter a := by
  first | exact @GlobalTheory.FlagZ.isSelfInter_comb_grLine_perm | exact GlobalTheory.FlagZ.isSelfInter_comb_grLine_perm | (intros; apply GlobalTheory.FlagZ.isSelfInter_comb_grLine_perm <;> assumption)
