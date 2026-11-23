import Mathlib
import Formalism.LocalToGlobal.ThresholdSelection
import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfFormalDegreeInput
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassNumberAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstTypePrimeLargeOfRecord
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExactRanksOfRecord
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimesOverOfNorm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeEqMassOfReal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RankConditionOfColumnsEqualSymmetricLevelStatement
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem exact_ranks_along_tied_family : (∀ D : D7, RT.MassRatioUnderVolume D) → ∀ (eps : ℝ) (Fm : FamP eps), Formalism.L2.TSelF Fm →
    ∀ C0 Cg cb Cu cT CT : ℝ, PX.RanksF Fm C0 Cg cb Cu cT CT := by
  intro hU eps Fm s C0 Cg cb Cu cT CT
  refine ⟨max s.1 (Fm.x1 + 1), fun x hx i hh => ?_⟩
  have hx1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) (le_trans (le_max_right _ _) hx)
  have R := s.2 x hx1 (le_trans (le_max_left _ _) hx) i
  have hr := R.T.theta.real
  have hm : ∀ u, StandardLattice.Mu0Tie (Fm.D x i) u := GlobalTheory.T.rankCondition_of_columns_equal_symmetricLevel _ R.T.cols
  have h4f : StandardLattice.Conclusion4f (Fm.D x i) (Fm.ex x hx1 i).lev :=
    StandardLattice.HarishChandraReduction.rankFormula_of_classNumber _ _ (ColClassNumber.classNumber_all _ _)
  obtain ⟨-, -, -, -, -, -, -, -, hT, -, h0, h1, -⟩ := hh.1
  have hS : ∀ j, StandardLattice.SplitsF (Fm.D x i) ((Fm.D x i).host.g j) :=
    Fin.forall_fin_two.2 ⟨RankSplit.splitsF_of_norm _ _ ((Fm.D x i).host.g_prime 0) h0,
      RankSplit.splitsF_of_norm _ _ ((Fm.D x i).host.g_prime 1) h1⟩
  exact exact_ranks_of_record (Fm.D x i) hS (RankVolume.definiteSpaceVolume_eq_mass_of_volumeComparison (fun D => hU D) _ hr)
    (StandardLattice.factDstar_fam Fm x hx1 i)
    (fun u => h4f (first_type_prime_large_of_record _) hS u
      (RankSplit.splitsF_of_norm _ _ ((Fm.D x i).mem u).A.T_prime (hT u).1) (hm u))

end GlobalTheory
