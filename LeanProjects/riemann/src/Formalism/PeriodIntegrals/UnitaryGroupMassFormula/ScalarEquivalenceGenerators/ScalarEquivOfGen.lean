import Mathlib
import Formalism.PeriodIntegrals.ScalPairs

noncomputable section

open scoped Classical

namespace PI.UnitaryGroupMassFormula.ScalarEquivalenceHermitianSpace

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.ScalPairs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finrank_VS (D : D7) : finrank D.host.E (VS D).V = D.R.k + 2 * D.R.rS + 1 := by
  have h1 := (VS D).rank_eq
  have h2 : (VS D).rank = D.R.rankY 0 := D.sp.Y_rank 0 (Nat.zero_le _)
  obtain ⟨j, hj⟩ := D.R.m_even
  have hm2 := D.R.two_le_m
  rw [h1, h2]
  simp only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS, zero_mul, add_zero]
  omega

theorem tu_ne_zero (D : D7) (u : D.what₂.Word) : ((Tu D u : ℕ) : D.host.E) ≠ 0 := by
  rw [Ne, Nat.cast_eq_zero]
  exact (D.mem u).A.T_prime.ne_zero

theorem scalarEquiv_of_gen (h : ScalarEquivG) (D : D7) (u u' : D.what₂.Word) : ScalarEquiv D u u' := by
  intro F0 Λ hΛ
  obtain ⟨_, hfix, _⟩ := hΛ
  obtain ⟨hlat, _, hlift, _⟩ := hfix
  have key := h D.host.E (VS D) D.R.rS D.R.k (gS D) (finrank_VS D) Λ hlat
    ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) (tu_ne_zero D u) (tu_ne_zero D u')
    (lf D F0) hlift
  refine ⟨fun x => ?_, fun {x y} hxy => ?_, fun {x y z} h1 h2 => ?_⟩
  · exact key.refl ⟨x.1.1, x.1.2.1, x.2⟩
  · exact key.symm (x := ⟨x.1.1, x.1.2.1, x.2⟩) (y := ⟨y.1.1, y.1.2.1, y.2⟩) hxy
  · exact key.trans (x := ⟨x.1.1, x.1.2.1, x.2⟩) (y := ⟨y.1.1, y.1.2.1, y.2⟩)
      (z := ⟨z.1.1, z.1.2.1, z.2⟩) h1 h2

end PI.UnitaryGroupMassFormula.ScalarEquivalenceHermitianSpace
