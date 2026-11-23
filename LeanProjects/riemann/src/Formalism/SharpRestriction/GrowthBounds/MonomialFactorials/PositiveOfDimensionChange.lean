import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.DirectionsOfPositivePart
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestDimBCProved

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def RestOpen6 (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestBCdim C0 CE1 CE2 X ∧ RestPlusB C0 CE1 CE2 X CM ∧ RestDirQ C0 CE1 CE2 X

def RestOpen6E (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → RestOpen6 C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem positive_of_dimension_change (D : Formalism.BasicNotions.D7) (h : RestOpen6E D) : RestOpen5E D :=
  thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hP Ckap Cs CM hCM X hA hH => by
    obtain ⟨a, b, c⟩ := hP Ckap Cs CM hCM X hA hH
    exact ⟨a, b, restDir_of c (restDimBC_proved C0 CE1 CE2 X)⟩) h

theorem closed_of_open_dimensions (D : Formalism.BasicNotions.D7) (h : RestOpen6E D) : IntegralityFromMetricForLargeConstants D :=
  closed_of_open_positive D (positive_of_dimension_change D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
