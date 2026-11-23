import Formalism.LocalToGlobal.GlobalTheory.GL4.ColumnLatticeExactSlope
import Formalism.LocalToGlobal.GlobalTheory.GL4.BranchingIntegralNormalised
import Formalism.LocalToGlobal.GlobalTheory.GL4.PShortFrame

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

theorem column_exact_slope_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : fam0 Fm ColSlopeEq :=
  ⟨0, fun _ _ _ _ => column_lattice_exact_slope _⟩

theorem lower_slope_inequality_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : FamilySlopeLowerOpenPart Fm :=
  familySlopeLowerOpen_of_std standard_slope_lower hook_length_bound Fm (column_exact_slope_family Fm)

theorem slope_proposition_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : ConclusionF5 Fm :=
  familySlopeLower_of_open Fm (lower_slope_inequality_family Fm)

theorem packet_of_third_proposition (h6 : Link6F) : KudlaFamilyOfMinkowskiTransference := by
  unfold Link6F at h6
  unfold KudlaFamilyOfMinkowskiTransference
  intro eps Fm hF hT _ hTr _
  unfold KudlaFamilyStatement AdmF ConclusionOnFamily
  rintro ⟨a1, a2, -, -, a6, -⟩
  exact ⟨family_mass_count_bound Fm, family_first_bound_of_theta Fm a2, theorem_three_family_large_constant Fm, family_bound_of_period_theta_lowering Fm a1 a2 a6, slope_proposition_family Fm,
    h6 eps Fm hF hT hTr, familySupBound_holds Fm, propZ_second_holds⟩

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
