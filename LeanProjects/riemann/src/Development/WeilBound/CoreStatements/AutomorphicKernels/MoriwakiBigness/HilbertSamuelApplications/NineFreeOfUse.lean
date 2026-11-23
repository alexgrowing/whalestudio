import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.HsLinksOfUse
import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.GrassmannianHeightBoundOfSystems
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NineFreeOfIntersection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem nineFree_of_use :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PositivityTheory.MbHsUse.HSUse → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → Prov.ZhangDimensionPushDownGrassmannianHeightBounds := by
  intro hI hU hBig hRes
  obtain ⟨-, -, -, -, hZ, hD⟩ := GlobalTheory.CompanionTheory.Ar.Giv.hsLinks_of_use hU hBig
  exact ⟨hZ, hD, trivial, GlobalTheory.T.push_down_of_arith_intersection_system hI, GlobalTheory.CompanionTheory.Ar.Giv.grassmannian_height_bound_of_systems hI hU hBig hRes⟩

end GlobalTheory.CompanionTheory.Ar.Link
