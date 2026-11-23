import Formalism.FlagUnipotentLattices.CoveringRadius2
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.NearFarVolumeBounds
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.KappaConstantAssembly

namespace Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds

theorem polarInv : Formalism.HermitianLatticeCounting.S7.PolarInv := Formalism.HermitianLatticeCounting.P.polar_decomposition_inverse
theorem allSumRate : Formalism.HermitianLatticeCounting.S7.AllSumRate := Formalism.HermitianLatticeCounting.P.all_sum_rate
theorem threshCount : Formalism.HermitianLatticeCounting.S7.ThreshCount := Formalism.HermitianLatticeCounting.P.threshold_count
theorem layerCount : Formalism.HermitianLatticeCounting.S7.LayerCount := Formalism.HermitianLatticeCounting.P.layer_count
theorem kappaAssembly : Formalism.HermitianLatticeCounting.S7.KappaAssembly := Formalism.HermitianLatticeCounting.P.kappa_constant_assembly
theorem logVolumeBound : Formalism.HermitianLatticeCounting.S7.LogVolumeBound := Formalism.HermitianLatticeCounting.P.log_volume_bound
theorem stepsRoom : Formalism.HermitianLatticeCounting.S7.StepsRoom := Formalism.HermitianLatticeCounting.P.room_for_iterations

end Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds
