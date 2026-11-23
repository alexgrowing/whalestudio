import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FglInvariant
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FormalGroupConstCoeffZero
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.BridgeK

universe u v

namespace Formalism.L2.Th1.A

theorem cubeTwoR : CubeTwoR.{u} := cube_two_relation
theorem cubeThreeR : CubeThreeR.{u} := cube_three_relation
theorem coeffMem : CoeffMem.{u} := coeffMem_of zSerMap halfLog

theorem shortInv : ShortInv := short_weierstrass_inverse
theorem wpNumEq : WpNumEq := wpNumEq_of wpShape wpRecursion
theorem uSerEq : USerEq := uSerEq_of wpShape wpRecursion

end Formalism.L2.Th1.A
