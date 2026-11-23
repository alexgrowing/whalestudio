import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlowOrbitFirstMinimumOfIsotropicFlowMajorant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flowOrbitFirstMinimum_of_isotropicFlowMajorant : FlowMajSt → OrbitThickSt := by
  first | exact @GlobalTheory.CuspFrom.OrbitThick.orbitThick_of_flowMaj | exact GlobalTheory.CuspFrom.OrbitThick.orbitThick_of_flowMaj | (intros; apply GlobalTheory.CuspFrom.OrbitThick.orbitThick_of_flowMaj <;> assumption)
