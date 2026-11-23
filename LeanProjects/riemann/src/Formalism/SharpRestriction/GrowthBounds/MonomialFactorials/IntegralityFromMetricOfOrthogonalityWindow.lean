import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestrictedBoundsWeakenFromNineToEight
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestBCdimOfYbc

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def OpenConditionsOrthogonal (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestOrth C0 CE1 CE2 X CM ∧ RestWin C0 CE1 CE2 X CM ∧ RestLvlDim C0 CE1 CE2 X

def OrthogonalityWindowLevelDimOnAdmissible (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → OpenConditionsOrthogonal C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem open_conditions_base_change (D : Formalism.BasicNotions.D7) (hY : RestYbc) (h : OrthogonalityWindowLevelDimOnAdmissible D) : RestOpen9E D :=
  thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hP Ckap Cs CM hCM X hA hH => by
    obtain ⟨a, b, c⟩ := hP Ckap Cs CM hCM X hA hH
    exact ⟨restBClvl_of C0 CE1 CE2 X hY, a, b, c⟩) h

theorem integrality_from_metric_of_orthogonality_window (D : Formalism.BasicNotions.D7) (hY : RestYbc) (h : OrthogonalityWindowLevelDimOnAdmissible D) : IntegralityFromMetricForLargeConstants D :=
  theorem_A_closed_of_nine_open_bounds D (open_conditions_base_change D hY h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
