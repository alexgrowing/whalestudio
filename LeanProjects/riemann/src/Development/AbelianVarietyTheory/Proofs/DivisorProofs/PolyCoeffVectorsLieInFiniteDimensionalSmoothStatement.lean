import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyCoeffVectorsLieInFiniteDimensionalSmooth
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyCoeff_vectors_lie_in_finiteDimensional_smooth : GlobalTheory.PsCo.Pc3.UFin := by
  first | exact @GlobalTheory.PsCo.Pc3.uFin | exact GlobalTheory.PsCo.Pc3.uFin | (intros; apply GlobalTheory.PsCo.Pc3.uFin <;> assumption)
