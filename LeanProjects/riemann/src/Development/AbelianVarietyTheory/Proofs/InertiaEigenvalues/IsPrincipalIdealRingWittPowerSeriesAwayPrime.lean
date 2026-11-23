import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsPrincipalIdealRingOfIsLocalization
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isPrincipalIdealRing_away_l : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    IsPrincipalIdealRing (Localization.Away (l : bk.S)) := by
  intro l _ K bk
  have h : (l : bk.S) = C ((l : ℕ) : Wq l bk.a) := (map_natCast C l).symm
  rw [h]
  exact GlobalTheory.ChartRing.isPrincipalIdealRing_away_C (WittVector.irreducible l (k := Fq l bk.a)) _

end GlobalTheory.BSP
