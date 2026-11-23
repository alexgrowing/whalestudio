import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.ClassMapInjectiveBijectiveNorms
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.WachRestrictionOfLiftingPackage
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions

theorem local_input_one_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm1 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm1
  exact Formalism.MainNotions.DeltaInvariantLattices.wach_free_of_properties (first_clause_of_local_package D HW F Cm h56)

theorem local_input_two_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm2 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm2
  exact second_clause_of_local_package D HW F Cm h56

theorem local_input_three_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm3 D HW F Cm := by
  unfold Formalism.MainNotions.LiftingTheory.adm3
  exact third_clause_of_local_package D HW F Cm h56

theorem local_input_four_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.ArchimedeanSignatureMatching D HW F Cm := by
  unfold Formalism.MainNotions.LiftingTheory.ArchimedeanSignatureMatching
  exact fourth_clause_of_local_package D HW F Cm h56

theorem local_input_five_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm5 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm5
  exact fifth_clause_of_local_package D HW F Cm h56

theorem local_input_six_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm6 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm6
  exact sixth_clause_of_local_package D HW F Cm h56

theorem local_input_seven_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm7 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm7
  exact seventh_clause_of_local_package D HW F Cm h56

theorem local_input_eight_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm8 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm8
  exact eighth_clause_of_local_package D HW F Cm h56

theorem local_input_nine_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm9 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm9
  exact delta_invariants_of_local_package D HW F Cm h56

theorem local_input_ten_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm10 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm10
  exact Formalism.MainNotions.DeltaInvariantLattices.wach_characterisation_of_tenth (tenth_clause_of_local_package D HW F Cm h56)

theorem local_input_eleven_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm11 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm11
  exact Formalism.MainNotions.DeltaInvariantLattices.gamma_semisimple_local_of_consequences (consistency_of_local_package D HW F Cm h56)

theorem local_input_twelve_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm12 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm12
  exact second_first_of_local_package D HW F Cm h56

theorem local_input_thirteen_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm13 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm13
  exact second_b_of_local_package D HW F Cm h56

theorem local_input_fourteen_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm14 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm14
  exact second_c_of_local_package D HW F Cm h56

theorem local_input_fifteen_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm15 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm15
  exact second_dual_of_local_package D HW F Cm h56

theorem local_input_sixteen_of_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h56 : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) :
    Formalism.MainNotions.LiftingTheory.adm16 D HW F := by
  unfold Formalism.MainNotions.LiftingTheory.adm16
  exact lemma_three_of_local_package D HW F Cm h56

theorem class_map_naturality_of_herr (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h : Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F) : Formalism.MainNotions.LiftingTheory.adm21 D HW F := by
  intro l _ K s LL hg
  obtain ⟨hA, -, hN⟩ := h l K s LL hg
  refine ⟨hN, fun _ hl => ?_⟩
  intro T T' f pr pr' hpr
  have h2 : Formalism.MainNotions.LocalSituation.ell (Formalism.MainNotions.LocalSituation.sit D.loc HW l (D.locA l) K s LL hg) = 2 →
      ∃ i : (Formalism.MainNotions.LocalSituation.sit D.loc HW l (D.locA l) K s LL hg).K, i ^ 2 = -1 := by
    intro h2
    exact absurd (((D.loc l).PD_p K).symm.trans h2) hl
  exact ((hA h2 T).2.2 T' f pr pr' hpr).symm

end Formalism.MainNotions.N
