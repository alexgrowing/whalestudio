import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HodgeTateJumpsAtModulesForSign
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfWindows
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemTwistedDualJumpsWithoutBlockIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CcMulSelf
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem rat_jump_sets_eq_int_multisets : ∀ (D : D7) (i : D.nd.Loc) (ρ : D.what₂.Tau) (g : D.R.GG) (ep up : Bool), LJ.PlaceOf D ρ g → (up = true ↔ LJ.TypeU D ep g) → ∀ a : ℤ, ((a : ℚ) ∈ LJ.dualS (LJ.JJ D up (D.nd.j i) ρ) ↔ a ∈ jT1 (hcAt D g) (liftIdx D i) (pos (if ep then 1 else -1) g)) ∧ ((a : ℚ) ∈ LJ.dualS (LJ.JW D up (D.nd.j i) ρ) ↔ a ∈ jT2 (hcAt D g) (liftIdx D i) (pos (if ep then 1 else -1) g)) := by
  intro D i ρ g ep up hpl hup a
  have hP : hcAt D g = D.hc ρ := hcAt_eq_hc D ρ g hpl
  have hs : pos (if ep then 1 else -1) g = up := by
    unfold LJ.TypeU at hup
    rw [Formalism.HC.Frame.mem_Psi_iff] at hup
    rcases Int.units_eq_one_or g.1.2 with h | h <;> cases ep <;> cases up <;> simp_all [pos]
  have hsz : LJ.sz D (D.nd.j i) ρ = (D.hc ρ).e (liftIdx D i) := by
    have := D.nd.j_range i
    unfold LJ.sz liftIdx
    rw [dif_pos (by omega)]
  have hc0 : LJ.c0 D = ((D.R.t : ℚ) - 1) / 2 := rfl
  obtain ⟨h2, h1⟩ := jumps_rat (D.hc ρ) (liftIdx D i) up a
  rw [hP, hs, h1, h2]
  have hblk : ∀ x : ℤ, (∃ c : ℕ, c < D.R.t ∧ (x : ℚ) = (c : ℚ)) ↔ ∃ c : ℕ, c < D.R.t ∧ x = c := by
    intro x
    refine exists_congr fun c => and_congr Iff.rfl ?_
    exact_mod_cast Iff.rfl
  have hblk' : ∀ x : ℤ, (∃ c : ℕ, c < D.R.t ∧ (D.R.t : ℚ) - 1 - (x : ℚ) = (c : ℚ)) ↔ ∃ c : ℕ, c < D.R.t ∧ x = c := by
    intro x
    constructor
    · rintro ⟨c, hc, h⟩
      refine ⟨D.R.t - 1 - c, by omega, ?_⟩
      have h' : (D.R.t : ℤ) - 1 - x = c := by exact_mod_cast h
      push_cast [show c ≤ D.R.t - 1 by omega, show 1 ≤ D.R.t by omega]
      omega
    · rintro ⟨c, hc, rfl⟩
      refine ⟨D.R.t - 1 - c, by omega, ?_⟩
      push_cast [show c ≤ D.R.t - 1 by omega, show 1 ≤ D.R.t by omega]
      ring
  cases up
  · simp only [LJ.dualS, LJ.JJ, LJ.JW, LJ.cloudT, LJ.lowT, LJ.Jm, LJ.Jp, LJ.reflS, LJ.refl, LJ.cloudJ, LJ.lowJ,
      LJ.blockJ, Set.mem_setOf_eq, Set.mem_union, Bool.false_eq_true, if_false, hsz, hc0]
    refine ⟨or_congr Iff.rfl ?_, by push_cast⟩
    have := hblk' (-a - 1)
    push_cast at this
    exact this
  · simp only [LJ.dualS, LJ.JJ, LJ.JW, LJ.cloudT, LJ.lowT, LJ.Jm, LJ.Jp, LJ.reflS, LJ.refl, LJ.cloudJ, LJ.lowJ,
      LJ.blockJ, Set.mem_setOf_eq, Set.mem_union, if_true, hsz, hc0]
    refine ⟨or_congr Iff.rfl ?_, by push_cast⟩
    have := hblk (-a - 1)
    push_cast at this
    exact this

end GlobalTheory.HTW.Rec
