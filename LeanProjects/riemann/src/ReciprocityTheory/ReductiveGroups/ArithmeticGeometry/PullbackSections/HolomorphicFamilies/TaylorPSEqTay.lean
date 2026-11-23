import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.AnChart

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped ContDiff

theorem expS_zero' (k : Type) [CommRing k] [Algebra ℚ k] {n d : ℕ} : FB.expS k (0 : PS k n d) = 1 := by
  unfold FB.expS
  have ha : PowerSeries.HasSubst (0 : PS k n d) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have h0 : PowerSeries.constantCoeff (PowerSeries.exp k - 1) = 0 := by
    rw [map_sub, PowerSeries.constantCoeff_exp, map_one, sub_self]
  have e : PowerSeries.exp k = 1 + (PowerSeries.exp k - 1) := by ring
  rw [e, ← PowerSeries.coe_substAlgHom ha, map_add, map_one, PowerSeries.coe_substAlgHom ha,
    PowerSeries.subst_zero_of_constantCoeff_zero h0, add_zero]

private theorem hL0_lemma {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB ℂ d O) (w0 : O) :
    B.hL ℂ 0 w0 = 0 := by
  unfold FB.hL
  unfold ev
  simp [MvPowerSeries.subst, MvPowerSeries.eval₂]

theorem nabVal_additive {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB ℂ d O)
    (hF : ∀ i, B.G.F i = addF ℂ d i) (w0 : O) (m : ℕ) {θ : (Fin d → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0)
    {ι : Type} [Fintype ι] (u : ι → Fin d → ℂ) (P : MvPolynomial ι ℂ) :
    B.nabVal ℂ 0 w0 m (tay θ 0) u P = ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u θ 0 := by
  have hL0 : B.hL ℂ 0 w0 = 0 := hL0_lemma B w0
  have hK : B.FK ℂ = addF ℂ d := by
    funext i
    unfold FB.FK
    unfold FGLaw.mapF
    simp [hF]
  rw [FB.nabVal, hL0, smul_zero, expS_zero', mul_one, hK]
  exact constantCoeff_dpolyOf_tay hθ u P

end ReciprocityTheory.ChartRestriction.G.PullbackSections
