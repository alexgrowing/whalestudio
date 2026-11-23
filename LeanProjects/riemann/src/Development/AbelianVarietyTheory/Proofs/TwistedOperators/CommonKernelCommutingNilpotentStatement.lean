import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CommonKernelCommutingNilpotent
import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.common_kernel_commuting_nilpotent : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (T : ℕ → Module.End ℂ V) (S : Submodule ℂ V), FiniteDimensional ℂ S → S ≠ ⊥ → (∀ k, ∀ v ∈ S, T k v ∈ S) → (∀ k l, Commute (T k) (T l)) → (∀ k, ∀ v ∈ S, ∃ N : ℕ, (T k ^ N) v = 0) → ∃ v ∈ S, v ≠ 0 ∧ ∀ k, T k v = 0 := by
  first | exact @GlobalTheory.exists_common_null_of_commute_locallyNilpotent | exact GlobalTheory.exists_common_null_of_commute_locallyNilpotent | (intros; apply GlobalTheory.exists_common_null_of_commute_locallyNilpotent <;> assumption)
