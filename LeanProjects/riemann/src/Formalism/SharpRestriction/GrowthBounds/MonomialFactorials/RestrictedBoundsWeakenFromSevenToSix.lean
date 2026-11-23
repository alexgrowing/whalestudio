import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.PositiveOfDimensionChange
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BejjSmulLeft

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def RestOpen7 (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestBCdim C0 CE1 CE2 X ∧ RestOrth C0 CE1 CE2 X CM ∧ RestWin C0 CE1 CE2 X CM ∧ RestDirQ C0 CE1 CE2 X

def RestOpen7E (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → RestOpen7 C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem restricted_bounds_weaken_from_seven_to_six (D : Formalism.BasicNotions.D7) (h : RestOpen7E D) : RestOpen6E D :=
  thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hP Ckap Cs CM hCM X hA hH => by
    obtain ⟨a, b, c, d⟩ := hP Ckap Cs CM hCM X hA hH
    have hY0 : (0 : ℝ) < X.L.Y := by linarith [hH.1.1]
    exact ⟨a, restPlusB_of CM hY0 b c, d⟩) h

theorem closed_of_open_base_dims (D : Formalism.BasicNotions.D7) (h : RestOpen7E D) : IntegralityFromMetricForLargeConstants D :=
  closed_of_open_dimensions D (restricted_bounds_weaken_from_seven_to_six D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
