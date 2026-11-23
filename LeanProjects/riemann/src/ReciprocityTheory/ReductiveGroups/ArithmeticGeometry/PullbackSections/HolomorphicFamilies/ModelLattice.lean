import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ModelLat

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLat

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA
  ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatB FractionalIdeal

variable {r : ℕ}

theorem xi_zero_eq_host (D : D7) : D.host.xi0 =
    D.host.sqrtMinusD / ((Ideal.absNorm D.host.ccK : D.host.E) * (D.host.d : D.host.E)) := by
  have hN : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hd4 : 2 ≤ D.host.d := by have := D.host.qd_big.2; omega
  have hd : (D.host.d : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hs2 := Formalism.BasicNotions.Host.sqrtMinusD_sq D.host
  have hs : D.host.sqrtMinusD ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hs2
    exact hd (neg_eq_zero.1 hs2.symm)
  unfold Host.xi0
  rw [div_eq_div_iff (mul_ne_zero hN hs) (mul_ne_zero hN hd)]
  linear_combination (-(Ideal.absNorm D.host.ccK : D.host.E)) * hs2

end ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLat
