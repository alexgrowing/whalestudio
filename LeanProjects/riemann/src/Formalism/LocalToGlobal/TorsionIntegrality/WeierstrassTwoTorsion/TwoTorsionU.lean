import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.TwoTorsionIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.BridgeJ

universe u v

namespace Formalism.L2.Th1.A

theorem twoTorsionZ : TwoTorsionZ.{u} := two_torsion_integral
theorem plusZ : PlusZ.{u} := addition_integral
theorem wpInU : WpInU.{u} := wpInU_of wpShape
theorem tInZ : TInZ.{u} := tInZ_of wpShape

theorem bridgeWp : BridgeWp := bridgeWp_of wpCleared
theorem bridgeLaw : BridgeLaw := bridgeLaw_of coeffMem fglLog halfSpec halfLog
theorem bridgeCurve : BridgeCurve := bridgeCurve_of coeffMem wpInU cubeTwoR
theorem bridgeTwo : BridgeTwo := bridgeTwo_of coeffMem tInZ twoTorsionZ

end Formalism.L2.Th1.A
