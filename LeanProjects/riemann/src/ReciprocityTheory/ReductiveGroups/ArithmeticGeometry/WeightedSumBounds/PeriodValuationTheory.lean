import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.RootStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.FactorialWeightedSumBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.OmBStatement

namespace ReciprocityTheory.ChartRestriction.G.Sh

def TypicalCurveTheory : Prop :=
  CoprimeMultiplicationBijective ∧ TypicalCurveEigenspace ∧ TypicalCurveBasisExists ∧ TypicalCurveTangentBasis ∧ TypicalCurveStructureConstants ∧ TypicalCurveValuationBounds ∧
    TypicalCurveRebasing ∧ RootStatement ∧ LowAStatement ∧ LowBStatement ∧ FactorialWeightedSumBound ∧
    FactorialMultiindexBound ∧ RadiusExponentInequality

def PeriodValuationTheory : Prop := OmStatement

theorem a9 : PeriodValuationTheory := om

end ReciprocityTheory.ChartRestriction.G.Sh
