import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfB

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem gradNCondition : Formalism.MainNotions.N.Ln34.GradNStep := by
  intro D HW F Cm CA CB CK hA l hlp hl K LL hG π' E hR T h' hh' hT
  have h1 : adm1 D HW F Cm := hA.1
  rcases Nat.eq_zero_or_pos (sK l K) with hs0 | hs
  ·
    apply gradNPf_small
    simp [MK, hs0]
  · obtain ⟨f, t, x, u, -, -, hf, ht, hE, hΔ, hγ, hK, hN⟩ :=
      gradNPf_hyps D HW F Cm h1 l hl K LL hG π' E hR T hT hs
    rcases le_or_gt (MK l K h') 1 with hM | hM
    · apply gradNPf_small
      exact hM
    · obtain ⟨a, ha⟩ := hN (MK l K h' - 1)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ MK l K h')] at ha
      refine gradNPf_local (hf := hf) (ht := ht) (hu := hE) (hπΔ := hΔ) (hγN := hγ) (hK := hK)
        (hM := by omega) (a := a) (ha := ?_)
      convert ha using 2
      · rw [(D.loc l).PD_p K]
      · rfl

end Formalism.MainNotions.N.Ln34

end
