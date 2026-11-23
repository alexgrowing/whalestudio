import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.FamilyPartFiveOfExplicitConstants
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.DivisionRationalLattice
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremThreeHypothesesOfMultiplicity
import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
import Formalism.LocalToGlobal.GlobalTheory.GL5.LocalEndomorphismContinuous

noncomputable section

namespace Formalism.MainNotions.StandardLattice.HarishChandraReduction

open Formalism.BasicNotions Formalism.MainNotions

theorem content_bound_clause (D : D7) (Lv : LevelData D) : adm17 D Lv :=
  column_lemma_of_definite_form D Lv (UnusedSlot33.division_rational_lattice D) (GlobalTheoryTheory.gram0Def D)

theorem admissible_bound_family_holds {eps : ℝ} (Fm : FamP eps) : FamilyLevelConditionAdmitted Fm :=
  fun x _ i => content_bound_clause (Fm.D x i) _

theorem levels_pro_g_on_columns (D : D7) (Lv : LevelData D) : Conclusion4p D Lv :=
  Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.levels_pro_g D Lv

theorem column_stabilisers_trivial (D : D7) (Lv : LevelData D) : SmallOrderPrimeLogSumBound D Lv :=
  levelDimension_of_admissible D Lv (content_bound_clause D Lv) (levels_pro_g_on_columns D Lv)

theorem rankFormula_of_classNumber (D : D7) (Lv : LevelData D) (hn : ClassNumberFormula₂ D Lv) : Conclusion4f D Lv :=
  level_rank_of_trivial_stabilisers D Lv (column_stabilisers_trivial D Lv) hn

theorem landherrSmall_of_hasse (D : D7) (h : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.LandherrHasse D) : LandherrSmall D := by
  let _ := D.host.cmStar
  intro W hW hsig _
  obtain ⟨b, -, hb⟩ := h W hW hsig
  exact ⟨b, hb⟩

theorem part_four_of_class_number_landherr (D : D7) (Lv : LevelData D) (C3 : ℝ) (hn : ClassNumberFormula₂ D Lv) (hs : LandherrSmall D) :
    ThetaChernBoundOfLastLine D Lv C3 :=
  levelStatement_remaining D Lv C3 (levels_pro_g_on_columns D Lv) hn hs

theorem levelStatement_of_adm17 (D : D7) (Lv : LevelData D) (C3 : ℝ) (h2 : VolumeMass D) (h3 : PointsLemma D C3) (hn : ClassNumberFormula₂ D Lv)
    (hs : LandherrSmall D) : StandardLatticeProperties D Lv C3 :=
  part_four_of_class_number_landherr D Lv C3 hn hs h2 h3 (content_bound_clause D Lv)

section Fam

variable {eps : ℝ} (Fm : FamP eps)

theorem part_four_family_of_class_number_landherr (C3 : ℝ)
    (hn : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev)
    (hs : ∀ x (i : Fm.Ix x), LandherrSmall (Fm.D x i)) : LiftNormFamilyStatement Fm C3 :=
  familyLevel_remaining Fm C3 (fun _ _ _ => levels_pro_g_on_columns _ _) hn hs

theorem lemma_four_family_of_landherr_small_ranks (C3 : ℝ) (h2 : FamilyMassVolumeBounds Fm) (h3 : FamilyTheoremThree Fm C3)
    (hn : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev)
    (hs : ∀ x (i : Fm.Ix x), LandherrSmall (Fm.D x i)) : FamilyPartFour Fm C3 :=
  part_four_family_of_class_number_landherr Fm C3 hn hs h2 h3 (admissible_bound_family_holds Fm)

theorem familyRankFormula_of_classNumber (hn : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev) :
    ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Conclusion4f (Fm.D x i) (Fm.ex x hx i).lev :=
  fun x hx i => rankFormula_of_classNumber _ _ (hn x hx i)

theorem chosenProviso_4f (C0 : ℝ) (hC0 : Real.exp 1 ≤ C0)
    (h4f : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Conclusion4f (Fm.D x i) (Fm.ex x hx i).lev)
    (hR : RankTiesF Fm) : ChosenProviso Fm C0 := by
  obtain ⟨x2, hR⟩ := rankHypF_of Fm hR
  refine ⟨max (Fm.x1 + 1) x2, fun x hx i => ?_⟩
  have e1 : Fm.x1 < x := by
    have := (le_max_left (Fm.x1 + 1) x2).trans hx
    linarith
  exact LinkB.proviso_mono _ (Real.exp_pos 1) hC0
    (proviso_e (Fm.L x i) (LinkB.rank_formula_of_part_four _ (h4f x e1 i) (hR x ((le_max_right _ _).trans hx) i))
      (StandardLattice.factDuStar_fam Fm x e1 i) (StandardLattice.factDstar_fam Fm x e1 i))

theorem chosenProviso_min (C0 : ℝ) (hC0 : Real.exp 1 ≤ C0)
    (hn : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev)
    (hR : RankTiesF Fm) : ChosenProviso Fm C0 :=
  chosenProviso_4f Fm C0 hC0 (familyRankFormula_of_classNumber Fm hn) hR

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem explicitConstants_family_of_volume_eq_mass (h2v : flipTwoThree.fam0 Fm BaseVolumeEqualsMass) (h3 : flipTwoThree.fam0 Fm SigmaDegreeTwoSidedBoundOfGap) : FamilyVandermondeCountExplicit Fm :=
  division_level_prime_family Fm (Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.siegel_mass_ratio_family Fm) h2v h3

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem familyWeylLaw_of_packet (h2v : flipTwoThree.fam0 Fm BaseVolumeEqualsMass) (h3 : flipTwoThree.fam0 Fm SigmaDegreeTwoSidedBoundOfGap) : PartFiveFamilyBounds Fm :=
  GlobalTheoryTheory.family_part_five_of_explicit_constants Fm (explicitConstants_family_of_volume_eq_mass Fm h2v h3)

end Fam

def cTmin (y : ℝ) : ℝ := max 11 (16 + 3 * max 5 (y + 1))

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem tuSize_min {eps : ℝ} (Fm : FamP eps) (hle : cTmin Fm.CYL ≤ Fm.CTu)
    (h2v : flipTwoThree.fam0 Fm BaseVolumeEqualsMass) (h3 : flipTwoThree.fam0 Fm SigmaDegreeTwoSidedBoundOfGap) : TuSize Fm := by
  obtain ⟨x0, hx0⟩ := explicitConstants_family_of_volume_eq_mass Fm h2v h3 (max 5 (Fm.CYL + 1)) (max 5 (Fm.CYL + 1))
  obtain ⟨x1, hx1⟩ := GlobalTheoryTheory.rowsAF_fam Fm (max 5 (Fm.CYL + 1))
  refine GlobalTheoryTheory.tuSize_fam Fm (cTmin Fm.CYL) (max x0 x1) (fun x hx hxx i => ?_) hle
  exact part_five_all_of_explicit _ _ _ _ _ (hx0 x (le_trans (le_max_left _ _) hx) hxx i)
    (fun Δ w hB => hx1 x (le_trans (le_max_right _ _) hx) hxx i Δ w hB) (le_max_left _ _) (le_max_right _ _)

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem tuSize_sup_min (eps : ℝ) :
    ∃ cT : ℝ → ℝ, ∀ Fm : FamP eps, cT Fm.CYL ≤ Fm.CTu → flipTwoThree.fam0 Fm BaseVolumeEqualsMass → flipTwoThree.fam0 Fm SigmaDegreeTwoSidedBoundOfGap → TuSize Fm :=
  ⟨cTmin, fun Fm hle h2v h3 => tuSize_min Fm hle h2v h3⟩

section Fam3

variable {eps : ℝ} (Fm : FamP eps)

theorem familyLowestKType_of_multOne (hL : DiscreteSeriesWeylDimension.LowKMultOne) : ∀ x (i : Fm.Ix x), FamilyMassLastLine (Fm.D x i) :=
  fun x i => lowest_K_type_dimension_of_multiplicity (Fm.D x i) hL

theorem stabiliser_family_of_definite (hF : ∀ x (i : Fm.Ix x), PlaceDegreeData.DiscreteSeriesLowestKTypeFormula (Fm.D x i)) (hL : DiscreteSeriesWeylDimension.LowKMultOne) : FamilyTheoremThreeAdmitted Fm :=
  fun x i => theorem_three_hypotheses_of_multiplicity (Fm.D x i) (hF x i) hL

theorem theorem_three_family_of_formal_degree (C3 : ℝ) (hC3 : 1 ≤ C3)
    (hHC : ∀ x (i : Fm.Ix x), Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.HCFormalDegree (Fm.D x i)) (hL : DiscreteSeriesWeylDimension.LowKMultOne) :
    FamilyTheoremThreeGeneral Fm C3 :=
  fun x i => Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.theorem_three_all_unitary (Fm.D x i) C3 hC3 (Fm.ties x i).cdScale_tie (hHC x i)
    (lowest_K_type_dimension_of_multiplicity (Fm.D x i) hL)

theorem theorem_three_family_of_formal_degree_input (C3 : ℝ) (hC3 : 1 ≤ C3) (hHC : RT.HCFdegR) (hL : DiscreteSeriesWeylDimension.LowKMultOne) :
    FamilyTheoremThreeGeneral Fm C3 :=
  theorem_three_family_of_formal_degree Fm C3 hC3 (fun x i => RT.hcFormalDegree_of_R hHC (Fm.D x i)) hL

theorem familyRestriction_of_harishChandra (hHC : ∀ x (i : Fm.Ix x), Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.HCFormalDegree (Fm.D x i))
    (hL : DiscreteSeriesWeylDimension.LowKMultOne) (hE : DiscreteSeriesWeylDimension.DiscreteSeriesExists) : FamilySigmaDegreeTwoSidedBound Fm :=
  fun x i => Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.discrete_series_statement (Fm.D x i) (Fm.ties x i).cdScale_tie (Fm.ties x i).dsig_tie (hHC x i)
    weylForK_holds hL hE

theorem familyFormalDegree_of_harishChandra (C3 : ℝ) (hC3 : 8192 ≤ C3)
    (hHC : ∀ x (i : Fm.Ix x), Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.HCFormalDegree (Fm.D x i))
    (hL : DiscreteSeriesWeylDimension.LowKMultOne) (hE : DiscreteSeriesWeylDimension.DiscreteSeriesExists) : FamilyTheoremThree Fm C3 :=
  fun x i => theorem_three_sigma_of_explicit (Fm.D x i) C3 hC3 (familyRestriction_of_harishChandra Fm hHC hL hE x i)

theorem slopeEstimate_of_lemmaB_slopeLine_alt (D : D7) (hT : VolTie D) (hU : RT.MassRatioUnderVolume D) (hv : RT.GenusMassUnderVolume D) : VolumeMass D :=
  volumeMass_of_definiteVolume D (volumeMass_of_unfolding D (hU hT)) (hv hT)

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem massStatement_of_classData (D : D7) (hT : VolTie D) (hV : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolRatioTrue D)
    (hI0 : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt D 0) (hI1 : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt D 1)
    (hI2 : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt D 2) : VolumeMass D :=
  ⟨Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.theorem_two_of_volume_ratio D hV hT, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.volume_mass_of_items D hT hV hI0 hI1 hI2,
    Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.standardLattice_aux2b D, massIdentity_holds D⟩

theorem familyOpNorm_of_sup_jet_alt (tVol : VolTieF Fm) (hU : ∀ x (i : Fm.Ix x), RT.MassRatioUnderVolume (Fm.D x i))
    (hv : ∀ x (i : Fm.Ix x), RT.GenusMassUnderVolume (Fm.D x i)) : FamilyMassVolumeBounds Fm :=
  fun x i => slopeEstimate_of_lemmaB_slopeLine_alt (Fm.D x i) (tVol x i) (hU x i) (hv x i)

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem lemma_two_family_of_class_conditions (tVol : VolTieF Fm) (hV : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolRatioTrueF Fm)
    (hI : ∀ x (i : Fm.Ix x), Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt (Fm.D x i) 0 ∧
      Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt (Fm.D x i) 1 ∧ Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt (Fm.D x i) 2) : FamilyMassVolumeBounds Fm :=
  fun x i => massStatement_of_classData (Fm.D x i) (tVol x i) (hV x i) (hI x i).1 (hI x i).2.1 (hI x i).2.2

end Fam3

section Inputs

variable {eps : ℝ} (Fm : FamP eps)

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem familyWeylLaw_of_inputs (tVol : flipTwoThree.fam0 Fm VolTie) (hV : flipTwoThree.fam0 Fm Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolRatioTrue)
    (hI2 : flipTwoThree.fam0 Fm fun D => Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt D 2)
    (hHC : ∀ x (i : Fm.Ix x), Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.HCFormalDegree (Fm.D x i)) (hL : DiscreteSeriesWeylDimension.LowKMultOne)
    (hE : DiscreteSeriesWeylDimension.DiscreteSeriesExists) : PartFiveFamilyBounds Fm :=
  familyWeylLaw_of_packet Fm (Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.volume_eq_mass_family Fm tVol hV hI2)
    (Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.discrete_series_of_formal_degree Fm ⟨0, fun x _ _ i => hHC x i⟩ weylForK_holds hL hE)

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem tuSize_of_inputs (hle : cTmin Fm.CYL ≤ Fm.CTu) (tVol : flipTwoThree.fam0 Fm VolTie)
    (hV : flipTwoThree.fam0 Fm Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolRatioTrue)
    (hI2 : flipTwoThree.fam0 Fm fun D => Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt D 2)
    (hHC : ∀ x (i : Fm.Ix x), Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.HCFormalDegree (Fm.D x i)) (hL : DiscreteSeriesWeylDimension.LowKMultOne)
    (hE : DiscreteSeriesWeylDimension.DiscreteSeriesExists) : TuSize Fm :=
  tuSize_min Fm hle (Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.volume_eq_mass_family Fm tVol hV hI2)
    (Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.discrete_series_of_formal_degree Fm ⟨0, fun x _ _ i => hHC x i⟩ weylForK_holds hL hE)

theorem familyLevel_of_landherrHasse (C3 : ℝ) (h2 : FamilyMassVolumeBounds Fm) (h3 : FamilyTheoremThree Fm C3)
    (hn : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev)
    (hLH : ∀ x (i : Fm.Ix x), Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.LandherrHasse (Fm.D x i)) : FamilyPartFour Fm C3 :=
  lemma_four_family_of_landherr_small_ranks Fm C3 h2 h3 hn fun x i => landherrSmall_of_hasse _ (hLH x i)

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem familyLevel_of_inputs (C3 : ℝ) (hC3 : 8192 ≤ C3) (tVol : VolTieF Fm) (hV : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolRatioTrueF Fm)
    (hI : ∀ x (i : Fm.Ix x), Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt (Fm.D x i) 0 ∧
      Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt (Fm.D x i) 1 ∧ Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt (Fm.D x i) 2)
    (hHC : ∀ x (i : Fm.Ix x), Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.HCFormalDegree (Fm.D x i)) (hL : DiscreteSeriesWeylDimension.LowKMultOne)
    (hE : DiscreteSeriesWeylDimension.DiscreteSeriesExists)
    (hn : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev)
    (hLH : ∀ x (i : Fm.Ix x), Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.LandherrHasse (Fm.D x i)) : FamilyPartFour Fm C3 :=
  familyLevel_of_landherrHasse Fm C3 (lemma_two_family_of_class_conditions Fm tVol hV hI) (familyFormalDegree_of_harishChandra Fm C3 hC3 hHC hL hE) hn hLH

end Inputs

end Formalism.MainNotions.StandardLattice.HarishChandraReduction

end
