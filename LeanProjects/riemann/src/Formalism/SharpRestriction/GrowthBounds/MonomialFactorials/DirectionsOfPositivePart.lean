import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ThresholdsMonoNormalized
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.PlusAWICondition

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def RestOpen5 (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestBCdim C0 CE1 CE2 X ∧ RestPlusB C0 CE1 CE2 X CM ∧ RestDir C0 CE1 CE2 X

def RestOpen5E (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → RestOpen5 C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem directions_of_positive_part (D : Formalism.BasicNotions.D7) (h : RestOpen5E D) : RestOpen4E D :=
  thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hP Ckap Cs CM hCM X hA hH => by
    obtain ⟨a, b, c⟩ := hP Ckap Cs CM hCM X hA hH
    exact ⟨a, plusACondition C0 CE1 CE2 X CM, b, c⟩) h

theorem closed_of_open_positive (D : Formalism.BasicNotions.D7) (h : RestOpen5E D) : IntegralityFromMetricForLargeConstants D :=
  closed_of_open_directions D (directions_of_positive_part D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
