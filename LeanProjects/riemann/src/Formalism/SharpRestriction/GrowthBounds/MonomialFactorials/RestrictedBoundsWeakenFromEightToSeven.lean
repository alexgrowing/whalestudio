import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestrictedBoundsWeakenFromSevenToSix
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.MemLevelsIff

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def RestOpen8 (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestBClvl C0 CE1 CE2 X ∧ RestOrth C0 CE1 CE2 X CM ∧ RestWin C0 CE1 CE2 X CM ∧ RestDirQ C0 CE1 CE2 X

def RestOpen8E (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → RestOpen8 C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem restricted_bounds_weaken_from_eight_to_seven (D : Formalism.BasicNotions.D7) (h : RestOpen8E D) : RestOpen7E D :=
  thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hP Ckap Cs CM hCM X hA hH => by
    obtain ⟨a, b, c, d⟩ := hP Ckap Cs CM hCM X hA hH
    exact ⟨restBCdim_of C0 CE1 CE2 X a, b, c, d⟩) h

theorem theorem_A_closed_of_eight_open_bounds (D : Formalism.BasicNotions.D7) (h : RestOpen8E D) : IntegralityFromMetricForLargeConstants D :=
  closed_of_open_base_dims D (restricted_bounds_weaken_from_eight_to_seven D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
