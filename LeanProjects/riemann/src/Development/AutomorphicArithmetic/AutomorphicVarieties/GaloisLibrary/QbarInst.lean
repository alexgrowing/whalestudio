import Mathlib

namespace UpperTheory.V.QbarInst

theorem charZero : CharZero (AlgebraicClosure ℚ) := inferInstance

theorem torsionFree : Module.IsTorsionFree ℚ (AlgebraicClosure ℚ) := inferInstance

theorem algClosure : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ

end UpperTheory.V.QbarInst
