import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.TwoTorsionU
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.ChainRuleFormalGroupVar
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.XPowSuccDvdOfDerivative

universe u v

namespace Formalism.L2.Th1.A

theorem zMap : ZMap.{u, v} := z_series_map_spec
theorem jetMem : JetMem.{u} := jet_mem'
theorem wpPrimeShape : WpPrimeShape.{u} := weierstrass_p_prime_shape

theorem expAdd : ExpAdd.{u} := expSeriesAdd
theorem plusZCleared : PlusZCleared.{u} := plusZCleared_of plusZ tInZ

end Formalism.L2.Th1.A
