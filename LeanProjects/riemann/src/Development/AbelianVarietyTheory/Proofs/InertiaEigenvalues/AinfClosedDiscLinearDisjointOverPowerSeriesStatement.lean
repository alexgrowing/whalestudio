import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedDiscLinearDisjointOverPowerSeries
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_closedDisc_linearDisjoint_over_powerSeries : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (sA : bk.S →+* A) (ι : Type) (TB : TopBasis sA bk.J ι) (j : bk.DS bk.ρ₀ →+* Disc l (sA X) bk.ρ₀), IsDiscMap sA j → ∀ (x y : A) (f g : bk.DS bk.ρ₀), g ≠ 0 → y ≠ 0 → toDisc l (sA X) bk.ρ₀ x * j g = toDisc l (sA X) bk.ρ₀ y * j f → ∃ δ a : bk.S, δ ≠ 0 ∧ sA δ * x = sA a * y := by
  first | exact @GlobalTheory.BSP.linDisjoint_disc | exact GlobalTheory.BSP.linDisjoint_disc | (intros; apply GlobalTheory.BSP.linDisjoint_disc <;> assumption)
