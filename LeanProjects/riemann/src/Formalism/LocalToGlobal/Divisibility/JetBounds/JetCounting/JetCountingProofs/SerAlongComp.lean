import Formalism.LocalToGlobal.Divisibility.JetBounds.JetCounting.RelShape
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.TwoPlaces

noncomputable section

namespace Formalism.L2.DIV.C

open Formalism.DworkPowerSeriesWeights (Integral mvExp serAlong)
open Formalism.InvariantFactorPaths.G7 (Simeq)
open MvPowerSeries
open Formalism.L2.Th1.D.BiextensionAlongSeries Formalism.L2.Th1.D.TwoPlaceCoordinateLemmas

section Field

variable {K : Type} [Field K]

theorem hs0 {α β : Type} [Finite α] {u : α → MvPowerSeries β K} (h : ∀ a, constantCoeff (u a) = 0) : HasSubst u :=
  hasSubst_of_constantCoeff_zero h

end Field

section Normed

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

end Normed

end Formalism.L2.DIV.C
