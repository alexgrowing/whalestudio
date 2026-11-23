import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneIndexOfOneClassOfSupportOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symData_oneIndex_of_oneClass_of_supportOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.OneClass t ν → S.SupportOne t → S.OneIndex t ν := by
  first | exact @GlobalTheory.SymChain.oneIndex_of_oneClass_of_supportOne | exact GlobalTheory.SymChain.oneIndex_of_oneClass_of_supportOne | (intros; apply GlobalTheory.SymChain.oneIndex_of_oneClass_of_supportOne <;> assumption)
