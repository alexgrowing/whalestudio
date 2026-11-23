import Mathlib
import Formalism.PeriodIntegrals.KerLat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerCoordinatesZero.IntCoordsZero

theorem kernel_lattice_t0_exists : PI.KerLat.ExistsTwoTorsionOffKernels :=
  PI.TwoDivisibility.main
