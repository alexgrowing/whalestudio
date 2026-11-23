import Formalism.GradedWeylDivisibility.StatementB
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LGradedLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem row_divided_closed_graded : RowDivClosedGraded := by
  intro r n M hM f hf μ
  obtain ⟨h, hhM, hh⟩ := lgraded_multi M hM μ Finset.univ f hf
  convert hhM using 1
  ext m
  rw [coeff_weightedHomogeneousComponent, hh]
  congr 1
  apply propext
  constructor
  · intro hm a _
    rw [← lgraded_weight_rowW, hm]
  · intro hm
    funext a
    rw [lgraded_weight_rowW]
    exact hm a (Finset.mem_univ a)

end Formalism.GradedWeylDivisibility
