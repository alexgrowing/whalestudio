import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibLieLatticeFull
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
open NumberField ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiFib_lie_lattice_full : ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K), Full F.lieLat := by
  first | exact @GlobalTheory.LieHt.SemiFib.full_lieLat | exact GlobalTheory.LieHt.SemiFib.full_lieLat | (intros; apply GlobalTheory.LieHt.SemiFib.full_lieLat <;> assumption)
