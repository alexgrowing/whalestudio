import Mathlib
import Formalism.PeriodIntegrals.JetsPhW

universe u_1

namespace Bl.FirstLemmaG

theorem goal1 :
  ∀ {p : Nat} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F : MvPowerSeries.{u_1, 0} σ (PadicComplex p)} (i : σ),
  PI.JetsPhW.IntegralMv.{u_1} F →
    PI.JetsPhW.IntegralMv.{u_1}
      (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} (MvPowerSeries.pderiv.{u_1, 0} (PadicComplex p) i) F) := by
  intro p _ σ F i hF n
  show ‖MvPowerSeries.coeff n (MvPowerSeries.pderiv (PadicComplex p) i F)‖ ≤ 1
  rw [MvPowerSeries.coeff_pderiv, norm_mul]
  have h1 : ‖MvPowerSeries.coeff (n + Finsupp.single i 1) F‖ ≤ 1 := hF _
  have h2 : ‖((n i : PadicComplex p) + 1)‖ ≤ 1 := by
    have := IsUltrametricDist.norm_natCast_le_one (PadicComplex p) (n i + 1)
    rwa [Nat.cast_succ] at this
  calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

end Bl.FirstLemmaG
