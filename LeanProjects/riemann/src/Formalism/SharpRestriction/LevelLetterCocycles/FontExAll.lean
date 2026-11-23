import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def FontExAll (D : D7) (HW : HWOf D.loc) (_F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (hG : Good K s LL)
    (T₀ T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L),
    IsSESLat (Qp := ℚ_[l]) ι π →
    Function.Injective (((HW l).W K s LL hG).map ι) ∧ Function.Surjective (((HW l).W K s LL hG).map π) ∧
      ∀ x, ((HW l).W K s LL hG).map π x = 0 ↔ ∃ y, ((HW l).W K s LL hG).map ι y = x

end Formalism.MainNotions.N.Ln34

end
