import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ExpRules
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSDivMem
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExistsXPowMul
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.PtTransRec
import Formalism.SharpRestriction.LevelLetterCocycles.TruncationClauseOfLatticeHypotheses
import Formalism.SharpRestriction.LevelLetterCocycles.DlOfQp
import Formalism.SharpRestriction.LevelLetterCocycles.RingHypothesesOfCrystalline
import Formalism.SharpRestriction.LevelLetterCocycles.EvaluationAtUniformizerPower
import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
import Formalism.SharpRestriction.LevelLetterCocycles.IsFracOL
import Formalism.SharpRestriction.LevelLetterCocycles.JumpsInLetterOfEvenIndex
import Formalism.SharpRestriction.LevelLetterCocycles.At0HomApply
import Formalism.SharpRestriction.LevelLetterCocycles.CompleteMax
import Formalism.SharpRestriction.LevelLetterCocycles.RingClausesAtUniformizer
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowerCongruenceOfAdmitted
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsAdicCompleteOfLe

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.bigCellDetWeightedEnergyIntegral

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

theorem dual_lemma_of_admitted (hA : admitted D HW F Cm CR CA CB CK) (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l)
    (hg : Loc.Good K 1 LL) [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))] : LemmaDN ((HW l).W K 1 LL hg) := by
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
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := Formalism.MainNotions.RamifiedCoefficientChains.S9.DLev.complete_max LL
  have hring : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W :=
    (((h9 _ (Formalism.MainNotions.LiftingTheory.gen_one_crys W)) hs hCA.2.2).2.2 (Formalism.MainNotions.UnusedSlot80.finrank_K0_eq_one_of_le_Kur hCAl.1)).1
  have C := ((Cm l).C K 1 LL hg).tie
  have hG := Formalism.MainNotions.N.Pv.LocalLengthBound.gam_of_tie W hs C
  have hLev : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W := (level_tools_of_admitted' D HW F Cm hA l K LL hCAl h5l).2
  have hRu : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules W := Formalism.MainNotions.N.Pv.LocalLengthBound.expRules_of W hLev hG.1 hG.2
  have hRing : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing W := Formalism.MainNotions.N.Pv.LocalLengthBound.expRing_of W hring
  have hpt := Formalism.MainNotions.UnusedSlot80.points_exist_of_ring_condition D HW F (uniformizer_clause_of_admitted D HW F Cm hA)
  have hL := Formalism.MainNotions.UnusedSlot80.levCoeff_of_pt D HW F Cm (laurent_clause_of_admitted' D HW F Cm hA) hpt
  have hBall : ∀ (l' : ℕ) [Fact l'.Prime] (K' LL' : FinExt l') (hg' : Good K' 1 LL')
      [NeZero (Module.finrank ℚ_[l'] ↥(K0 K'))], Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool ((HW l').W K' 1 LL' hg') := by
    intro l' _ K' LL' hg' _
    haveI : IsFractionRing ↥(OL LL') ↥LL'.1 := Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL'
    exact Formalism.MainNotions.RamifiedCoefficientChains.Sh.basTool_of _ (hA.1 l' K' 1 LL' hg').2.2.2.2.2.2.2.2.1
  have hEC : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit W :=
    Formalism.MainNotions.N.Pv.LocalLengthBound.expCrit_D' D HW F Cm CR CA CB CK hA hL hBall l K LL hCAl h5l
  have hGM := Formalism.MainNotions.RamifiedCoefficientChains.S9.GM.gMem_of W hE hC hQ h1.2.2.2.2.1 h9 hRu hEC
  have hBas : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool W := Formalism.MainNotions.RamifiedCoefficientChains.Sh.basTool_of W h9
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
  have hTH : Formalism.MainNotions.CrystallineLiftingInputs.THor W := Formalism.MainNotions.CrystallineLiftingInputs.Tools.frobenius_power_congruence_local D HW F Cm hA.1 l K LL hg
  have hZ := Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.zTool_of W h9 (((Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData.truncation_clause_of_lattice_hypotheses D HW F Cm (uniformizer_clause_of_admitted D HW F Cm hA) hA.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.2.2.2.1).2 l K LL hg).2) hTH hBas hRu
    hRing hΔ
  have hAd : Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB.AdaptBas W :=
    Formalism.MainNotions.RamifiedCoefficientChains.S9.AdM.adaptBas_of W hE hC hQ h1.2.2.1 h1.2.2.2.2.1 h9 (Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL)
  have hpm : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    rw [hpl]; exact Formalism.BasicNotions.Examples₂.LB.l_mem_max LL
  have hPt : Formalism.MainNotions.LiftingTheory.CaseA W → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1),
      IsPrimitiveRoot ζ ((D.loc l).PD K).p →
      ∃ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Formalism.MainNotions.LiftingTheory.Over W τ i ∧ Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hg i ζ τ := by
    intro _ c ζ hζ
    obtain ⟨τ, hτ⟩ := hpt l K LL hCAl h5l c ζ (by rwa [hpl] at hζ)
    refine ⟨τ, ?_, hτ⟩
    obtain ⟨τs, ⟨hemb, -⟩, hres⟩ := hτ
    apply AlgHom.ext
    intro x
    have hy : (x : Om l) ∈ Ks K 1 := (le_sup_left : K0 K ≤ Ks K 1) x.2
    show τ (algebraMap ↥(K0 K) ↥K.1 x) = _
    rw [hres (algebraMap ↥(K0 K) ↥K.1 x) ⟨x, hy⟩ rfl]
    exact hemb x ⟨x, hy⟩ rfl
  have hDT : Formalism.MainNotions.RamifiedCoefficientChains.Sh.DetTool W :=
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.detTool_of W h9 _ h1.2.2.2.1 hPt hQ hpm hset.2.2.2.2.1
  have hDet := Formalism.MainNotions.RamifiedCoefficientChains.S9.DetA.detAlg_of W hE hC hQ h1.2.2.2.2.1 h9 hBas (fun _ => hDT)
    (Formalism.MainNotions.RamifiedCoefficientChains.S9.GCoord.gCoord_holds W)
  exact Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.lemmaDN_of_S1E W hZ hAd hGM hDet d T₁ T₂ F' b S η m hset

end Formalism.MainNotions.RamifiedCoefficientChains.S9.bigCellDetWeightedEnergyIntegral
