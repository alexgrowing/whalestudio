import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.HaarTransfer.SchurClosable
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurUnitaryInner.UnitaryInner

theorem schur_closable : Formalism.IndefR.Leaf.SchurClosable :=
  PI.UnitaryGroupMassFormula.SchurClosable.Main.schurClosable
