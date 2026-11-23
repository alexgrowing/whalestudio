import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestrictedBoundsWeakenFromEightToSeven
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestDirOfLvl

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def RestOpen9 (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestBClvl C0 CE1 CE2 X ∧ RestOrth C0 CE1 CE2 X CM ∧ RestWin C0 CE1 CE2 X CM ∧ RestLvlDim C0 CE1 CE2 X

def RestOpen9E (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → RestOpen9 C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem restricted_bounds_weaken_from_nine_to_eight (D : Formalism.BasicNotions.D7) (h : RestOpen9E D) : RestOpen8E D :=
  thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hP Ckap Cs CM hCM X hA hH => by
    obtain ⟨a, b, c, d⟩ := hP Ckap Cs CM hCM X hA hH
    exact ⟨a, b, c, restDirQ_of d (restSumSpan_proved C0 CE1 CE2 X)⟩) h

theorem theorem_A_closed_of_nine_open_bounds (D : Formalism.BasicNotions.D7) (h : RestOpen9E D) : IntegralityFromMetricForLargeConstants D :=
  theorem_A_closed_of_eight_open_bounds D (restricted_bounds_weaken_from_nine_to_eight D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
