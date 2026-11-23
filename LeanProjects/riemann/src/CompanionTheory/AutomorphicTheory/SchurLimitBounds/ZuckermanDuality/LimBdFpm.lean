import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.Assemble
import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.BetaAtInfinityZero
import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.GeneratingFunctionPolynomial
import CompanionTheory.AutomorphicTheory.KFiniteVectors.KDecay
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.CoefEigOfInfChar
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.CoefCC

noncomputable section

namespace CompanionTheory.LimBd.Main

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP

theorem span_powers : SpanPow := mul_mem_spanBox_of_gap

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

end CompanionTheory.LimBd.Main
