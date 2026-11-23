import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem clusters_letterwise : ∀ {n : ℕ} (th : ZMod n → Prop) (j : ℕ), Clusters th j → ∀ t, th t →
    (∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ th (t - k)) ∨
      ∃ d : ℕ, 1 ≤ d ∧ d ≤ j ∧ th (t - d) ∧ ∀ k : ℕ, 1 ≤ k → k ≤ d + j → k ≠ d → ¬ th (t - k) := by
  intro n th j hC t ht
  obtain ⟨F, sp, hF, huniq⟩ := hC
  obtain ⟨x, ⟨hxF, hxt⟩, -⟩ := huniq t ht
  obtain ⟨hthx, hspj, -, -, hbetween, hbefore⟩ := hF x hxF
  rcases hxt with rfl | rfl
  · exact Or.inl hbefore
  · by_cases hsp0 : sp x = 0
    · left
      rw [hsp0, Nat.cast_zero, add_zero]
      exact hbefore
    · right
      refine ⟨sp x, Nat.one_le_iff_ne_zero.2 hsp0, hspj, by simpa using hthx, fun k hk1 hk2 hkd => ?_⟩
      rcases lt_or_gt_of_ne hkd with hlt | hgt
      · have e : x + (sp x : ZMod n) - k = x + ((sp x - k : ℕ) : ZMod n) := by
          rw [Nat.cast_sub hlt.le]
          ring
        rw [e]
        exact hbetween (sp x - k) (by omega) (by omega)
      · have e : x + (sp x : ZMod n) - k = x - ((k - sp x : ℕ) : ZMod n) := by
          rw [Nat.cast_sub hgt.le]
          ring
        rw [e]
        exact hbefore (k - sp x) (by omega) (by omega)

end GlobalTheory.HTW.Rec
