import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.HsLinksOfUse
import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.SelfIntersectionLeOfBoundedInjectionUse
import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.ArithmeticHilbertSamuelOfSystems
import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.SmallSectionsUpperOfUse
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeIndexOfIntersection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem provHS_of_use :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PositivityTheory.MbHsUse.HSUse →
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → Prov.HS := by
  intro hI hU hBig hRes
  obtain ⟨g1, z1, z2, g6p, -, -⟩ := GlobalTheory.CompanionTheory.Ar.Giv.hsLinks_of_use hU hBig
  exact ⟨z1, z2, g1, g6p, GlobalTheory.T.big_line_implies_height_positivity hBig, hU.g7p, GlobalTheory.CompanionTheory.Ar.Giv.smallSections_upper_of_use hI hU hRes,
    GlobalTheory.CompanionTheory.Ar.Giv.selfIntersection_le_of_boundedInjection_use hU hBig,
    GlobalTheory.CompanionTheory.Ar.Giv.arithmetic_hilbert_samuel_of_systems hI hU hBig hRes⟩

end GlobalTheory.CompanionTheory.Ar.Link
