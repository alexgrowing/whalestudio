import Formalism.SharpRestriction.LevelLetterCocycles.SecCritAll

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

def SecCrit0L (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL), CaseA K LL → 5 ≤ l →
    ∀ (A : Formalism.MainNotions.ArcLiftingSetup.ArcP (Module.finrank ℚ_[l] ↥(K0 K))), A.OK → ∀ c' ∈ A.cuts,
      ∀ T, Formalism.MainNotions.ArcLiftingSetup.Win ((HW l).W K 1 LL hG) A T → ∀ (d : ℕ) (b : Fin d → ((HW l).W K 1 LL hG).DD T)
        (sol : Fin d → ℕ → Fin d → ↥LL.1), Formalism.MainNotions.ArcLiftingSetup.IsHor ((HW l).W K 1 LL hG) T c' b sol →
          ∀ e : ℕ, LevC.SecCrit0 (W := (HW l).W K 1 LL hG) A c' e T b sol

theorem ctx_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h : AdmArcA D HW F Cm) (l : ℕ) [Fact l.Prime] (K LL : FinExt l)
    (hG : Good K 1 LL) (hCA : CaseA K LL) (h5l : 5 ≤ l) :
    haveI := neZero_finrank_max_unramified K
    LevC.Ctx ((HW l).W K 1 LL hG) := by
  obtain ⟨h3, -, h5, h9, hH, hTr, -, hSat⟩ := h
  have := neZero_finrank_max_unramified K
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have hCW : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hG) := caseA_of_unram' (D.loc l) (HW l) hG hCA.1 hCA.2.1
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p ≠ 2 := by rw [(D.loc l).PD_p]; exact hCA.2.1
  have hK := finrank_K0_eq_one_of_le_Kur hCA.1
  have hR := ring_condition_uniformizer_polynomial D HW F h9 l K LL hCA
  have hmod : ∀ T, IsCrys ((D.loc l).PD K) T.ρ → Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters ((HW l).W K 1 LL hG) T
      ((HW l).W K 1 LL hG).π₀ := fun T hT => ((h9 l K 1 LL hG T hT hs hp).2.2 hK).2
  have hc1 := Formalism.MainNotions.LiftingTheory.gen_one_crys ((HW l).W K 1 LL hG)
  have := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  have hΔ : IsUnit ((((HW l).W K 1 LL hG).DelF.card : ℕ) : ↥(OL LL)) :=
    cardΔ_of (W := (HW l).W K 1 LL hG) (not_isUnit_p ((HW l).W K 1 LL hG) (valRing_rec (D.loc l) LL))
      (card_DelF (W := (HW l).W K 1 LL hG) hs hp hK (h9 l K 1 LL hG _ hc1))
  have hV := valRing_rec (D.loc l) LL
  have h5p : 5 ≤ ((D.loc l).PD K).p := by rw [(D.loc l).PD_p]; exact h5l
  refine ⟨hCW.1, hs, hp, h5p, hR, h5 l K 1 LL hG, h3 l K 1 LL hG, hmod, hΔ, hSat l K LL hG hCA h5l,
    saturation_pullback_of_ring_condition D HW F h9 l K LL hG hCA h5l, hTr l K 1 LL hG, hH l K 1 LL hG, hV.1, hV.2.1, hV, ?_⟩
  intro h0
  have := congrArg (algebraMap (↥(OL LL)) ↥LL.1) h0
  rw [map_natCast, map_zero] at this
  exact Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero ((HW l).W K 1 LL hG) this

theorem membership_criterion_of_level_zero (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h : AdmArcA D HW F Cm) (h0 : SecCrit0L D HW) : SecCritL D HW := by
  intro l _ K LL hG hCA h5l
  have := neZero_finrank_max_unramified K
  have C := ctx_of D HW F Cm h l K LL hG hCA h5l
  intro _ _ A hA c hc e _ _ T hT d b sol hb
  have hc' : c - ((A.len c : ℕ) : ZMod _) ∈ A.cuts := ((hA.2.2.1 c hc).2.2).1
  exact LevC.secCrit_all C A hA _ hc' T hT b sol hb (h0 l K LL hG hCA h5l A hA _ hc' T hT d b sol hb) e

theorem arc_coordinates_of_level_zero (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h0 : SecCrit0L D HW) : ArcCoordinatesTheorem D HW F Cm := fun h =>
  arc_coordinates_of_membership D HW F Cm (membership_criterion_of_level_zero D HW F Cm h h0) h

end Formalism.MainNotions.UnusedSlot80
