import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.CocyclesToWachVectorsBoundOfExtTool
import Formalism.SharpRestriction.LevelLetterCocycles.FirstLiftOfUniformizerClause
import Formalism.SharpRestriction.LevelLetterCocycles.SecondLiftOfHypotheses
import Formalism.SharpRestriction.LevelLetterCocycles.ExtDataExtTool
import Formalism.SharpRestriction.LevelLetterCocycles.EvaluationAtUniformizerPower
import Formalism.SharpRestriction.LevelLetterCocycles.LocalClauseOfFrobeniusHyps
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LemKD
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.FilDimOf
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSDivMem
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExistsXPowMul
import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
import Formalism.SharpRestriction.LevelLetterCocycles.IsFracOL
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
import Formalism.SharpRestriction.LevelLetterCocycles.LevelClauseOfOpenTool
import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
import Formalism.SharpRestriction.LevelLetterCocycles.CompleteMax
import Formalism.SharpRestriction.LevelLetterCocycles.TruncationClauseOfLatticeHypotheses

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.LocalLemmasFromLiterature

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
variable {CR CA CB CK : ℝ}

theorem caseA_loc' {l : ℕ} [Fact l.Prime] {K LL : Loc.FinExt l} (hg : Loc.Good K 1 LL)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hg)) : Loc.CaseA K LL := by
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  refine ⟨fun x hx => ?_, by rw [← hpl]; exact hCA.2.2, hg⟩
  obtain ⟨y, hy⟩ := hCA.1.2 ⟨x, hx⟩
  have h2 := y.2.2
  have : ((y : ↥(K0 K)) : Om l) = x := congrArg Subtype.val hy
  rw [this] at h2
  exact h2

theorem laurent_clause_of_admitted' (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm :=
  fun l _ K s LL h => (hA.1 l K s LL h).2.2.2.1

theorem uniformizer_clause_of_admitted (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F :=
  fun l _ K s LL h => (hA.1 l K s LL h).2.2.2.2.2.2.2.2.1

theorem level_tools_of_admitted' (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.WachCoordinates.adm7 D HW F Cm :=
  Formalism.MainNotions.UnusedSlot80.tools_unramified_statement D HW F Cm ⟨fun l _ K s LL h => (hA.1 l K s LL h).2.2.1, laurent_clause_of_admitted' D HW F Cm hA,
    uniformizer_clause_of_admitted D HW F Cm hA⟩

set_option maxHeartbeats 0 in

theorem local_lemmas_of_literature (hA : admitted D HW F Cm CR CA CB CK) (h23 : Formalism.MainNotions.LiftingTheory.adm23 D HW F)
    (hHerr : Formalism.MainNotions.ElementDenominator.HerrClassNaturalExtension D.loc D.locA HW F) (a22 : Formalism.MainNotions.CrystallineLiftingBounds.adm22 D HW F)
    (hFont : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F) : cocyclesToWachVectorsBoundAtGoodExtensions D HW F := by
  intro l _ K LL hg _
  intro d T₁ T₂ F' b S η m hset
  have hCA : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hg) := hset.1
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hCAl : Loc.CaseA K LL := caseA_loc' D HW hg hCA
  have h5l : 5 ≤ l := by have := hset.2.1; rw [hpl] at this; omega
  set W := (HW l).W K 1 LL hg with hW
  have h1 := hA.1 l K 1 LL hg
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W := h1.2.2.2.2.2.2.2.2.1
  obtain ⟨hE, hC, hQ⟩ := hA.2.2.2.2.2.2.2.2.2.2.1 l K LL
  have hs : W.s = 1 := hCA.2.1
  haveI : IsFractionRing ↥(OL LL) ↥LL.1 := Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL
  haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  have hring : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W :=
    (((h9 _ (Formalism.MainNotions.LiftingTheory.gen_one_crys W)) hs hCA.2.2).2.2 (Formalism.MainNotions.UnusedSlot80.finrank_K0_eq_one_of_le_Kur hCAl.1)).1
  have C := ((Cm l).C K 1 LL hg).tie
  have hG := Formalism.MainNotions.N.Pv.LocalLengthBound.gam_of_tie W hs C
  have hLev : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W := (level_tools_of_admitted' D HW F Cm hA l K LL hCAl h5l).2
  have hRu : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules W := Formalism.MainNotions.N.Pv.LocalLengthBound.expRules_of W hLev hG.1 hG.2
  have hRing : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing W := Formalism.MainNotions.N.Pv.LocalLengthBound.expRing_of W hring
  have hpt := Formalism.MainNotions.UnusedSlot80.points_exist_of_ring_condition D HW F (uniformizer_clause_of_admitted D HW F Cm hA)
  have hL := Formalism.MainNotions.UnusedSlot80.levCoeff_of_pt D HW F Cm (laurent_clause_of_admitted' D HW F Cm hA) hpt
  have hBas : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool W := Formalism.MainNotions.RamifiedCoefficientChains.Sh.basTool_of W h9
  have hK : Formalism.MainNotions.RamifiedCoefficientChains.Sh.LemK W := Formalism.MainNotions.N.Pv.LocalLengthBound.lemK_D D HW F Cm CR CA CB CK hA hL l K LL hCAl h5l
  have hFD : Formalism.MainNotions.RamifiedCoefficientChains.Sh.FilDim W := Formalism.MainNotions.N.Pv.LocalLengthBound.filDim_of W hQ
  have hΔ : IsUnit ((W.DelF.card : ℕ) : ↥(OL LL)) := by
    have hcard : W.DelF.card = l - 1 :=
      Formalism.MainNotions.UnusedSlot80.LevR.card_delF D HW F (uniformizer_clause_of_admitted D HW F Cm hA) l K LL hCAl
    by_contra hnu
    have hm : ((W.DelF.card : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := hnu
    have hlm := Formalism.BasicNotions.Examples₂.LB.l_mem_max LL
    have e : ((l : ℕ) : ↥(OL LL)) - ((W.DelF.card : ℕ) : ↥(OL LL)) = 1 := by
      rw [hcard, Nat.cast_sub (by omega)]; simp
    have h3 := Submodule.sub_mem _ hlm hm
    rw [e] at h3
    exact (IsLocalRing.maximalIdeal.isMaximal ↥(OL LL)).ne_top ((Ideal.eq_top_iff_one _).2 h3)
  have hP9π : Formalism.MainNotions.LiftingTheory.P9π₀ W := (Formalism.MainNotions.LiftingTheory.uniformizer_ring_and_module_clauses W h9 hCA _ (Formalism.MainNotions.LiftingTheory.gen_one_crys W)).1
  have hRN : Formalism.MainNotions.LiftingTheory.CaseA W → Formalism.MainNotions.CrystallineLiftingInputs.RToolNum W := fun hCA' =>
    Formalism.MainNotions.CrystallineLiftingInputs.RToolNum_holds (D.loc l) (HW l) K LL hg hCA'
  have hDss : Formalism.MainNotions.RamifiedCoefficientChains.DssLet W := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 l K 1 LL hg
  have hS1 : Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step1 W :=
    Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.first_lift_of_uniformizer_clause W (Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL) hP9π hRN h9 hDss hRu hRing hK hFD
      hBas hE hC hQ
  have hTZ' : Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.TTool2Z W :=
    Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData.tTool2Z_DU D HW F (uniformizer_clause_of_admitted D HW F Cm hA) hA.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.2.2.2.1 l K LL hg
  have hFT : Formalism.MainNotions.CrystallineLiftingInputs.FTool W := Formalism.MainNotions.CrystallineLiftingInputs.Tools.local_clause_of_admitted_statements D HW F Cm hA l K LL hg
  have h2a : ∀ T : LocLat _ ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys _ T.ρ → Formalism.MainNotions.DeltaInvariantLattices.p2aK W T :=
    fun T hT => ((hA.2.2.1 l K 1 LL hg).1 T hT).2
  have hS2 : Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2 W :=
    Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.second_lift_of_hypotheses W hTZ' hFT hBas hK hFD hRing hRu h2a h1.2.2.2.2.1 h9 hE hC hQ
  have hQT : Formalism.MainNotions.CrystallineLiftingInputs.QTool W := Formalism.MainNotions.CrystallineLiftingInputs.Tools.level_clause_of_admitted_statements D HW F Cm hA h23 l K LL hg
  have hdex : W.DelF.card = ((D.loc l).PD K).p - 1 → ∃ dd : ↥(OL LL), dd * (W.DelF.card : ↥(OL LL)) = 1 :=
    fun _ => hΔ.exists_left_inv
  have hExt : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExtTool W :=
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.extData_extTool W (hHerr l K 1 LL hg).2.2.2 (Formalism.MainNotions.LiftingTheory.liftb_HExt_holds D HW F l K 1 LL hg)
      (Formalism.MainNotions.LiftingTheory.liftb_HOne_holds D HW F l K 1 LL hg) (Formalism.MainNotions.LiftingTheory.lker_HKer_D D HW F a22 l K 1 LL hg)
      (h23 l K LL) ((hFont l K LL hCAl).2.1) hdex h1.2.2.2.2.1 h1.2.2.2.2.2.1 h9 hQT
  exact Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.cocyclesToWachVectorsBound_of_extTool W hExt hS1 hS2 d T₁ T₂ F' b S η m hset

end Formalism.MainNotions.RamifiedCoefficientChains.S9.LocalLemmasFromLiterature
