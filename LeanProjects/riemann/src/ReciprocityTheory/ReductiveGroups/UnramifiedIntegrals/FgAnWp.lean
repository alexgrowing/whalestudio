import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.LatModel

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem shortW_map (l : ℕ) [Fact l.Prime] (g2 g3 : ℂ) (ι : ℂ ≃+* ℂ_[l]) :
    A.shortW (ι g2) (ι g3) = (A.shortW g2 g3).map (ι : ℂ →+* ℂ_[l]) := by
  ext <;> simp [A.shortW, WeierstrassCurve.map, map_ofNat]

theorem wp_bridge (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) :
    A.wpReg (A.shortW (ι L.g₂) (ι L.g₃)) = PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.pSeries L) := by
  have h1 := F.curveBridge (A.shortW L.g₂ L.g₃) L (A.shortInv ℂ _ _).2.1 (A.shortInv ℂ _ _).2.2.1
  have h2 := (A.zMap ℂ ℂ_[l] (ι : ℂ →+* ℂ_[l]) (A.shortW L.g₂ L.g₃)).2.2.1
  rw [← h1, h2, shortW_map]

end ReciprocityTheory.ChartRestriction.L1
