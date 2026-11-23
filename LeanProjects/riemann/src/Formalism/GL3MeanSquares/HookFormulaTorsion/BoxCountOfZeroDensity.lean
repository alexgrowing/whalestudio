import Mathlib
import Formalism.GL3MeanSquares.ZeroDensityBox
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailFinal
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountFinal

noncomputable section

namespace Formalism.HermitianLattices.ZeroDensityInBoxes

theorem box_tail_bound_all : BoxTailAll := Formalism.HermitianLattices.Ext.BoxTail.box_tail_bound

theorem box_count_of_zero_density : BoxCountOfZD := fun h =>
  Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.boxCountHyp_of_zeroDensityBox h

end Formalism.HermitianLattices.ZeroDensityInBoxes
