import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerVanishingBelowDimension

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

theorem GMod.quot_shift (F : GMod B R k) (s : R) (d : Deg k) :
    (F.shift d).quot s = (F.quot s).shift d := rfl

theorem GMod.ann_shift (F : GMod B R k) (s : R) (d d' : Deg k) :
    (F.shift d).ann s d' = (F.ann s d').shift d := by
  have h : ∀ m : Deg k, m - d' - d = m - d - d' := fun m => sub_right_comm m d' d
  unfold GMod.ann GMod.shift GMod.sub
  simp only [h]

theorem chi_shift (ts : List (Deg k × R)) : ∀ (F : GMod B R k) (d m : Deg k),
    chi ts (F.shift d) m = chi ts F (m - d) := by
  induction ts with
  | nil => intro F d m; rfl
  | cons p ts ih =>
    obtain ⟨d', s⟩ := p
    intro F d m
    simp only [chi]
    rw [GMod.quot_shift, GMod.ann_shift, ih, ih]

theorem ruleShift : RuleShift := fun _ _ ts F d m => chi_shift ts F d m

end Formalism.MainNotions.V.Pf.V2.Calc
