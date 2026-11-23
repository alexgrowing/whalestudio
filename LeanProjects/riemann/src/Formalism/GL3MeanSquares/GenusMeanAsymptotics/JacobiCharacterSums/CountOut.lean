import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZAll
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountFinal

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts

theorem boxCountHyp_outright : ∃ C : ℝ, Formalism.HermitianLattices.ZeroFreeRegionGL2.BoxCountHyp C :=
  boxCountHyp_of_zeroDensityBox ZD.zero_density_box

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
