import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FirstDeriv
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.ThmSUniform
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)

theorem ThmSUniform_of (hB : BetaIsG) (hK : CyclicPowerClassOfExpEquiv) (hM : MapSimeq) : ThmSUniform := by
  intro K0 _ _ _ _ p σ hU hζ F hF be hbe
  obtain ⟨c, hc, hcc, hsim⟩ := hB K0 p σ hU hζ F hF be hbe
  refine ⟨c, hc, hcc, hsim, ?_⟩
  intro K _ _ _ j ν r0 r1 _ hj om oms ϖ μ U0 Φ hϖ hom hμ0 hμ hU0 hΦ0 hΦ
  obtain ⟨hmap, hGs⟩ := hM K0 K (Fin 2) j hj
  have hp : ‖(p : K)‖ = (p : ℝ)⁻¹ := by
    rw [← hU.2.2.1, ← hj (p : K0), map_natCast]
  have hsim' : Simeq (MvPowerSeries.map j be) (Gser p (j c) (j (σ c))) := by
    rw [← hGs p c (σ c)]
    exact hmap _ _ hsim
  have hjc : ‖j c‖ ≤ 1 := by rw [hj]; exact hc
  have hjc' : ‖j (σ c)‖ ≤ 1 := by rw [hj]; exact norm_lift_le_one hU hc
  exact hK K p ν r0 r1 om oms (j c) (j (σ c)) ϖ μ U0 Φ (MvPowerSeries.map j be) hU.1 hp hϖ hom
    hjc hjc' hμ0 hμ hU0 hΦ0 hΦ hsim'

theorem theorem_s_uniform : ThmSUniform :=
  ThmSUniform_of Top.betaIsG Top.theorem_s_from_k_one Top.mapSimeq

theorem log_coordinates : LogCoord := by
  intro K _ p ϖ μ _ _ h0 h1
  have e1 := LogarithmEquivalence.subst_lgF_scale p ϖ
  have hμ : PowerSeries.HasSubst μ := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hX : PowerSeries.HasSubst (PowerSeries.C ϖ * PowerSeries.X : PowerSeries K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  have e2 := congrArg (fun f => (PowerSeries.subst μ f : PowerSeries K)) e1
  rw [PowerSeries.subst_comp_subst_apply hX hμ] at e2
  rw [← PowerSeries.coe_substAlgHom hμ, map_mul, map_mul, PowerSeries.coe_substAlgHom hμ, h1,
    PowerSeries.subst_X hμ] at e2
  have e3 : (PowerSeries.substAlgHom hμ) (PowerSeries.C ϖ : PowerSeries K) = PowerSeries.C ϖ := by
    have : (PowerSeries.C ϖ : PowerSeries K) = algebraMap K _ ϖ := rfl
    rw [this, AlgHom.commutes]
  rw [PowerSeries.coe_substAlgHom hμ] at e3
  rw [e3] at e2
  exact e2

theorem GcUnique_of (hD : DworkMv) (hFr : FrobExprG) : GcUnique := by
  intro K _ _ _ p σ hU c d hc hd hsim
  obtain ⟨hp, -, hnp, -, hσ⟩ := hU
  have hp2 : 2 ≤ p := hp.two_le
  have hpK : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hlin : Gser p c (σ c) - Gser p d (σ d) = Gser p (c - d) (σ (c - d)) := by
    simp only [Gser, map_sub]
    ring
  have hee : σ (σ (c - d)) = c - d := by rw [map_sub, map_sub, hc, hd]
  obtain ⟨h0, hI⟩ := hsim
  rw [hlin] at h0 hI
  have hDw := (hD K (Fin 2) p σ hp hnp hσ _ h0).1 hI
  rw [CoboundarySeries.map_Gser, hee, hFr K p (c - d) (σ (c - d)) hp2 hpK] at hDw
  have hl1 : PowerSeries.coeff 1 (lgF K p) = 1 := by
    have h := coeff_lgF_pow K hp2 0
    simpa using h
  have hg1 : PowerSeries.coeff 1 (g0F K p) = 0 := by
    by_contra h
    obtain ⟨j, hj⟩ := coeff_g0F_ne_zero h
    have h1 : p ∣ 1 := ⟨_, hj⟩
    have := Nat.le_of_dvd one_pos h1
    omega
  have hz : c - d = 0 := by
    apply CoboundarySeries.eq_zero_of_div hp2 hnp
    intro i
    have h := hDw (Finsupp.single 0 1 + Finsupp.single 1 (p * (p ^ 2) ^ i))
    have hn0 : (Finsupp.single 0 1 + Finsupp.single 1 (p * (p ^ 2) ^ i) : Fin 2 →₀ ℕ) 0 = 1 := by
      simp
    have hn1 : (Finsupp.single 0 1 + Finsupp.single 1 (p * (p ^ 2) ^ i) : Fin 2 →₀ ℕ) 1 =
        p * (p ^ 2) ^ i := by
      simp
    rw [MvPowerSeries.coeff_C_mul, map_sub, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul,
      coeff_product_single_variables (by decide) (by decide), coeff_product_single_variables (by decide) (by decide),
      hn0, hn1, hl1, hg1, coeff_g0F_of K hp2 i, zero_mul, mul_zero, zero_sub, one_mul, norm_mul,
      norm_neg, hnp] at h
    have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := by
      have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
      positivity
    exact le_of_mul_le_mul_left (by simpa using h) hpos
  exact sub_eq_zero.mp hz

theorem g_c_unique : GcUnique := GcUnique_of Top.dworkMv Top.frobExprG

end Formalism.InvariantFactorPaths.G7
