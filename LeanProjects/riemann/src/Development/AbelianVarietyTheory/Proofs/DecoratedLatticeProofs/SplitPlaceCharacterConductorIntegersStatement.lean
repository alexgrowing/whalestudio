import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceCharacter_conductor_integers : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), IsStdChar D ψ (-1) → p.IsChar ψ χ → p.UnitAA → GlobalTheory.SplitWeil.HasConductor χ 1 := by
  first | exact @GlobalTheory.SplitCharCond.hasConductor_one | exact GlobalTheory.SplitCharCond.hasConductor_one | (intros; apply GlobalTheory.SplitCharCond.hasConductor_one <;> assumption)
