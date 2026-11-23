import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.NzdOfCompOfConn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GGConn

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

theorem nonzero_divisor_of_connected : ReciprocityTheory.ChartRestriction.G.PullbackSections.NZDOfCompSt :=
  nzdOfComp_of_conn fun _ _ _ _ r X => (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r X).isPreconnected

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
