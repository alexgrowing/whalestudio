import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankFour
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective

namespace GlobalTheory.CompanionTheory.DSICKExp

theorem kExp : CompanionTheory.D.DSIC.KExp := by
  intro n ε g hg
  obtain ⟨Y, hY, he, -⟩ := Formalism.REAL.compact_exponential_surjective n ε g hg
  exact ⟨Y, hY, he.symm⟩

end GlobalTheory.CompanionTheory.DSICKExp
