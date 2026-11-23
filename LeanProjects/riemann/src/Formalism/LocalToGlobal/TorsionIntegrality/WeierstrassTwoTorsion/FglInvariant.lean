import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.WpShape
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FormalLogarithmBaseChange
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.SubstPairSubst

universe u v

namespace Formalism.L2.Th1.A

theorem wpShape : WpShape.{u} := wpShape_of expSpec wpODE
theorem wpCleared : WpCleared.{u} := wpCleared_of expSpec wpODE
theorem wpRecursion : WpRecursion.{u} := wpRecursion_of expSpec wpODE

theorem fglLog : FglLog.{u} := formal_group_logarithm
theorem fglGroup : FglGroup.{u} := formal_group_group_law
theorem fglInv : FglInv.{u} := formal_group_inverse

theorem zSerMap : ZSerMap.{u, v} := z_series_map
theorem zSerLog : ZSerLog.{u} := zSerLog_of fglLog
theorem zSerSpec : ZSerSpec.{u} := zSerSpec_of fglLog
theorem halfSpec : HalfSpec.{u} := halfSpec_of fglLog
theorem halfLog : HalfLog.{u, v} := halfLog_of fglLog fglLog

end Formalism.L2.Th1.A
