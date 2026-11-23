import Formalism.FlagUnipotentLattices.CuspidalityThreshold
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.OperatorHilbertSchmidtNorm

namespace Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts

theorem nearTotalAbs : Formalism.HermitianLatticeCounting.S7.NearTotalAbs := Formalism.HermitianLatticeCounting.P.near_region_total_abs
theorem cusp_threshold_bound : Formalism.HermitianLatticeCounting.S7.CuspidalityThreshold := Formalism.HermitianLatticeCounting.P.threshold_cusp_numeric
theorem threshCuspOp : Formalism.HermitianLatticeCounting.S7.ThreshCuspOp := Formalism.HermitianLatticeCounting.P.threshold_cusp_operator
theorem pZero : Formalism.HermitianLatticeCounting.S7.PZero := Formalism.HermitianLatticeCounting.P.probability_zero
theorem cubeMult : Formalism.HermitianLatticeCounting.S7.CubeMult := Formalism.HermitianLatticeCounting.P.cube_multiplication
theorem volLevel : Formalism.HermitianLatticeCounting.S7.VolLevel := Formalism.HermitianLatticeCounting.P.volume_level
theorem deepChainV : Formalism.HermitianLatticeCounting.S7.DeepChainV := Formalism.HermitianLatticeCounting.P.deep_region_chain_volume

end Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts
