import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsGaloisExtendingAlgHom
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.FinrankEqOneOfBijectiveBis
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SmulPowDifferenceIdentity
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LetterWindowBoundedBelow

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Module

section Record

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)

theorem arc_structures_three_hold {CR CA CB CK : ℝ} (hU : AdmBoundsB D HW F Cm CR CA CB CK)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL) (hK : CaseA K LL) :
    Formalism.MainNotions.N.FrobeniusPowerSeries.ArcSecMapCore ((HW l).W K 1 LL hG) ∧
      Formalism.MainNotions.N.FrobeniusPowerSeries.HorFrameCore ((HW l).W K 1 LL hG) ∧ Formalism.MainNotions.N.FrobeniusPowerSeries.ArcFilLowCore ((HW l).W K 1 LL hG) := by
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hFD : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have hH := hU.a2.2.2.2.2.2.1 l K 1 LL hG
  have hTr := hU.a2.2.2.2.2.2.2.1 l K 1 LL hG
  have hP9 := hU.p9 l K 1 LL hG
  refine ⟨arc_section_map _ Subtype.val_injective
    (fun x hx => ⟨⟨x, ((D.loc l).v_O LL x).1 hx⟩, rfl⟩) hP9 hH hTr
    (fun hp5 => (hU.a12 l K LL hG hK (hpl ▸ hp5)).1), horizontal_frame_structure _ hH hP9, arc_filtration_low _⟩

theorem arc_structures_hold_at {CR CA CB CK : ℝ} (hU : AdmBoundsB D HW F Cm CR CA CB CK) (hJ : UsedJ D HW F)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL) (hK : CaseA K LL) :
    Formalism.MainNotions.N.FrobeniusPowerSeries.ArcSecMapCore ((HW l).W K 1 LL hG) ∧ Formalism.MainNotions.N.FrobeniusPowerSeries.ArcGamLiftCore ((HW l).W K 1 LL hG) ∧
      Formalism.MainNotions.N.FrobeniusPowerSeries.HorFrameCore ((HW l).W K 1 LL hG) ∧ Formalism.MainNotions.N.FrobeniusPowerSeries.ArcFilLowCore ((HW l).W K 1 LL hG) :=
  have h3 := arc_structures_three_hold D HW F Cm hU l K LL hG hK
  ⟨h3.1, arc_gamma_lift_at D HW F Cm hU l K LL hG hK h3.2.2, h3.2.1, h3.2.2⟩

end Record

end Formalism.MainNotions.N.Ln17
