import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDerivedActionFiniteDimUnitaryRep
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivedAction_finiteDimUnitaryRep : ∀ (k : ℕ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)), PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) π → ∃ E : Fin k → Fin k → Module.End ℂ W, Formalism.REAL.GlRel E ∧ Formalism.REAL.IsUnitary (PI.UpqRep.allPos k) E ∧ ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ v, HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0 := by
  first | exact @GlobalTheory.UnitaryDerived.exists_derived_action | exact GlobalTheory.UnitaryDerived.exists_derived_action | (intros; apply GlobalTheory.UnitaryDerived.exists_derived_action <;> assumption)
