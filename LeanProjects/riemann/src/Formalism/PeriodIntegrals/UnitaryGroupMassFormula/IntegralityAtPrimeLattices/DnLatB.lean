import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.UpLatLoc0Of
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.DnLatKer
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.DnIncInt0Of

noncomputable section

open NumberField Ideal Matrix IsDedekindDomain

namespace PI.UnitaryGroupMassFormula.IAT

open Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Host Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.UG

variable {D : D7} {u : D.what₂.Word}

theorem dnLatLoc0_of_away (T : Forms0 D u) (hA : AwayLat0 T) : DnLatLoc0 T := by
  intro w hw hs v c g hg γ η κ hη hy hP B B' B₂ hB hB' hB₂ τ
  split_ifs with hτ
  · subst hτ
    have hk := lk_locP T.atT T.cls0 v c
    refine intInv_of_loc T.atT w hw hs v B₂ B' γ.1 hB₂ hB' ?_ ?_
    · rw [hP, ← hk]
      exact le_locP' _ _
    · rw [hk, ← hP]
      exact le_locP' _ _
  · obtain ⟨v', rfl⟩ : ∃ v', (D.fm u).tauOf w v' = τ := ⟨((D.fm u).tauOf w).symm τ, by simp⟩
    have hv' : v' ≠ v := fun h => hτ (h ▸ rfl)
    have hA' := hA v v' hv' c ((D.fm u).dn 0 v c g) γ η κ hη hy
    refine intInv_of_loc T.atT w hw hs v' B₂ B γ.1 hB₂ hB ?_ ?_
    · rw [hA']
      exact le_locP' _ _
    · rw [← hA']
      exact le_locP' _ _

end PI.UnitaryGroupMassFormula.IAT

end
