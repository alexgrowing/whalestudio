import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL4.PColSlopeEq
import Formalism.LocalToGlobal.Columns.PolyFnLemmas

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions.flipTwoThree

theorem translate_span_eq : TSpanEqVV := by
  intro K _ _ ι _ n lam
  unfold TSpan VV Formalism.GradedWeylDivisibility.tensorLat
  simp only [nablaSq_eq_delSq]
  rfl

theorem colSlopeEq_of_two (h2 : ZBasisStd) (D : D7) (h3 : QSlope D) : ColSlopeEq D := colSlopeEq_of translate_span_eq h2 D h3

theorem Link5F_of_two (h2 : ZBasisStd) (h3 : ∀ D, QSlope D) : Link5F := Link5F_of_three translate_span_eq h2 h3

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
