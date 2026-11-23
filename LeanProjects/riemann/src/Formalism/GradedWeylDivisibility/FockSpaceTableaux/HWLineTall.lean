import Formalism.GradedWeylDivisibility.StatementB
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwlineLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem highest_weight_line_tall : HWLineTall := by
  intro K _ _ r n ν ⟨s, hs, hνs⟩ f hf hdiv
  obtain ⟨hhom, hcol⟩ := (dualWeylPoint K r n ν f).mp hf
  refine lhwline_vanish f (fun a b hab => lhwline_rowGen_eq a b f (hdiv a b hab)) hcol ?_
  intro D hD
  exact lhwline_diag_tall ν s hs hνs f hhom D hD

end Formalism.GradedWeylDivisibility
