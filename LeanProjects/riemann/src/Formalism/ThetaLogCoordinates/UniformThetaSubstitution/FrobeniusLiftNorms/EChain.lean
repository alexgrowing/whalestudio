import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementJ
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.EJoint
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.NormLiftLeOne
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.OmegaOfTraceDuality

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp frameJet)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)

namespace ScaledSeriesSubstitution

theorem scale_scale {K ι : Type} [Field K] {ϖ : K} (hϖ : ϖ ≠ 0) (f : MvPowerSeries ι K) :
    MvPowerSeries.subst (fun i => MvPowerSeries.C ϖ * (MvPowerSeries.X i : MvPowerSeries ι K))
      (MvPowerSeries.subst
        (fun i => MvPowerSeries.C ϖ⁻¹ * (MvPowerSeries.X i : MvPowerSeries ι K)) f) = f := by
  ext n
  rw [MinorFormHomogeneity.coeff_subst_scale, MinorFormHomogeneity.coeff_subst_scale, ← mul_assoc, ← mul_pow,
    mul_inv_cancel₀ hϖ, one_pow, one_mul]

theorem hasSubst_scale {K ι : Type} [Field K] [Finite ι] (a : K) :
    MvPowerSeries.HasSubst
      (fun i => MvPowerSeries.C a * (MvPowerSeries.X i : MvPowerSeries ι K)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by simp

theorem subst_C_mul {K ι κ : Type} [Field K] {b : ι → MvPowerSeries κ K}
    (hb : MvPowerSeries.HasSubst b) (a : K) (f : MvPowerSeries ι K) :
    MvPowerSeries.subst b (MvPowerSeries.C a * f) = MvPowerSeries.C a * MvPowerSeries.subst b f := by
  rw [← MvPowerSeries.smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul, MvPowerSeries.subst_smul hb]

theorem constantCoeff_zLin {K : Type} [Field K] {ν r0 r1 : ℕ} [NeZero ν]
    (om oms : Fin ν → ZMod (2 * ν) → K) (x : Bool × EV ν r0 r1) :
    MvPowerSeries.constantCoeff (zLin om oms x) = 0 := by
  unfold zLin
  rw [map_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  split_ifs <;> simp

theorem subst_scale_zLin {K : Type} [Field K] {ν r0 r1 : ℕ} [NeZero ν]
    (om oms : Fin ν → ZMod (2 * ν) → K) (a : K) (x : Bool × EV ν r0 r1) :
    MvPowerSeries.subst
        (fun y => MvPowerSeries.C a * (MvPowerSeries.X y : MvPowerSeries (ZV ν r0 r1) K))
        (zLin om oms x) = MvPowerSeries.C a * zLin om oms x := by
  have hb := hasSubst_scale (K := K) (ι := ZV ν r0 r1) a
  unfold zLin
  rw [← MvPowerSeries.coe_substAlgHom hb, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MvPowerSeries.coe_substAlgHom hb]
  split_ifs
  · rw [subst_C_mul hb, MvPowerSeries.subst_X hb, mul_left_comm]
  · rw [← MvPowerSeries.coe_substAlgHom hb, map_zero, mul_zero]
  · rw [subst_C_mul hb, MvPowerSeries.subst_X hb, mul_left_comm]
  · rw [← MvPowerSeries.coe_substAlgHom hb, map_zero, mul_zero]

theorem ps_subst_C_mul {K κ : Type} [Field K] {w : MvPowerSeries κ K}
    (hw : PowerSeries.HasSubst w) (a : K) (f : PowerSeries K) :
    PowerSeries.subst w (PowerSeries.C a * f) = MvPowerSeries.C a * PowerSeries.subst w f := by
  rw [← PowerSeries.smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul, PowerSeries.subst_smul hw]

end ScaledSeriesSubstitution

open ScaledSeriesSubstitution

theorem kernel_bounds_of_uniform_exponent (hS : ThmSUniform) (h1 : KernelValuationBoundPadic) (h2 : KernelValuationBoundEvenSizes) (h3 : KernelB) :
    KernelBoundsOfUnramifiedExponent := by
  intro p _ K0 _ _ _ _ σ hU hζ F hF be hbe j ν r0 r1 _ hj om oms ϖ μ U0 Φ hϖ hom hμ0 hμ hU0 hΦ0 hΦ
    TT colN hts hp I n
  obtain ⟨c, hc, -, -, hcl⟩ := hS K0 p σ hU hζ F hF be hbe
  have hin := hcl ℂ_[p] j ν r0 r1 hj om oms ϖ μ U0 Φ hϖ hom hμ0 hμ hU0 hΦ0 hΦ
  have hp2 : 2 < p := hU.2.1
  have hpC : (p : ℂ_[p]) ≠ 0 := by exact_mod_cast hU.1.ne_zero
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    apply hpC
    rw [← hϖ, zero_pow]
    have : 2 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp2.le 2
    omega
  have hu : ∀ s : ZMod (2 * ν), ‖uS (j c) (j (σ c)) s‖ ≤ 1 := by
    intro s
    unfold uS
    split_ifs
    · rw [norm_neg, hj]
      exact norm_lift_le_one hU hc
    · rw [hj]
      exact hc
  have hin' : InClass (p : ℂ_[p]) (hhS p (uS (j c) (j (σ c)))) (MvPowerSeries.subst
      (fun x => MvPowerSeries.C ϖ * (MvPowerSeries.X x : MvPowerSeries (ZV ν r0 r1) ℂ_[p]))
      (thetaLog om oms ϖ μ (mvExp (-Φ) * U0))) := by
    unfold thetaLog
    rw [scale_scale hϖ0]
    exact hin
  exact ⟨h1 p ν r0 r1 _ ϖ _ TT colN hts hp I hp2 hϖ hu hin' n,
    h2 p ν r0 r1 _ ϖ _ TT colN hts hp I hp2 hϖ hu hin' n,
    fun i hi => h3 p ν r0 r1 i _ ϖ _ TT colN hts hp I hp2 hi hϖ hu hin' n⟩

theorem theta_log_coordinates : ThetaLogCoord := by
  intro K _ p ν r0 r1 _ om oms ϖ μ x hp hpK hϖ hμ0 hμ
  have hb := hasSubst_scale (K := K) (ι := ZV ν r0 r1) ϖ⁻¹
  have hz : PowerSeries.HasSubst (zLin om oms x : MvPowerSeries (ZV ν r0 r1) K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_zLin om oms x)
  have hw : PowerSeries.HasSubst
      (MvPowerSeries.C ϖ⁻¹ * zLin om oms x : MvPowerSeries (ZV ν r0 r1) K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by rw [map_mul, constantCoeff_zLin, mul_zero])
  have hm : PowerSeries.HasSubst (PowerSeries.C ϖ * μ : PowerSeries K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by rw [map_mul, hμ0, mul_zero])
  have e1 : MvPowerSeries.subst
      (fun y => MvPowerSeries.C ϖ⁻¹ * (MvPowerSeries.X y : MvPowerSeries (ZV ν r0 r1) K))
      (MvPowerSeries.C ϖ * sSub om oms μ x) =
      PowerSeries.subst (MvPowerSeries.C ϖ⁻¹ * zLin om oms x) (PowerSeries.C ϖ * μ) := by
    rw [subst_C_mul hb, ps_subst_C_mul hw]
    unfold sSub
    rw [FormalGroupLaws.subst_subst hb hz, subst_scale_zLin]
  have e2 := congrArg (fun f => (PowerSeries.subst (MvPowerSeries.C ϖ⁻¹ * zLin om oms x) f :
    MvPowerSeries (ZV ν r0 r1) K)) (log_coordinates K p ϖ μ hp hpK hμ0 hμ)
  rw [PowerSeries.subst_comp_subst_apply hm hw, ps_subst_C_mul hw ϖ PowerSeries.X,
    PowerSeries.subst_X hw,
    ← mul_assoc, ← map_mul, mul_inv_cancel₀ hϖ, map_one, one_mul] at e2
  rw [e1]
  exact e2

end Formalism.InvariantFactorPaths.G7
