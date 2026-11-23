import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRiemannianHaarOnSubgroupSigmaFiniteUnique
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvSubOneMem
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRiemannianHaarOnSubgroup_sigmaFinite_unique : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Subgroup (Formalism.REAL.UJ ε)), IsClosed (S : Set (Formalism.REAL.UJ ε)) → ∀ (d : ℕ) (μ : Measure (Formalism.REAL.UJ ε)), IsGaugeSub (S : Set (Formalism.REAL.UJ ε)) d μ → SigmaFinite μ ∧ IsFiniteMeasureOnCompacts μ ∧ ∀ μ', IsGaugeSub (S : Set (Formalism.REAL.UJ ε)) d μ' → μ' = μ := by
  first | exact @GlobalTheory.GaugeSubHaar.isGaugeSub_haar | exact GlobalTheory.GaugeSubHaar.isGaugeSub_haar | (intros; apply GlobalTheory.GaugeSubHaar.isGaugeSub_haar <;> assumption)
