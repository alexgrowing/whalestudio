import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementR
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.FirstLevelFromUniversalLaw
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Hurwitz
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.HurwitzB

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.G (unitBall)

section SlopeTestRemainingChoices

variable {K : Type} [Field K]

theorem coeff_one_subst1 (g : PowerSeries K) {a : PowerSeries K}
    (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.coeff 1 (PowerSeries.subst a g : PowerSeries K) =
      PowerSeries.coeff 1 g * PowerSeries.coeff 1 a := by
  have key : ∀ f : PowerSeries K, PowerSeries.coeff 1 f =
      PowerSeries.constantCoeff (PowerSeries.derivative K f) := by
    intro f
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
    simp
  rw [key, PowerSeries.derivative_subst (JetSubstitutionLemmas.hs1 ha), map_mul, JetSubstitutionLemmas.cc_subst1 ha, ← key, ← key]

theorem coeff_one_mulBy {l linv : PowerSeries K} (h : IsLogPair l linv) (a : K) :
    PowerSeries.coeff 1 (mulBy l linv a) = a := by
  have h0 : PowerSeries.constantCoeff (PowerSeries.C a * l) = 0 := by rw [map_mul, h.1, mul_zero]
  rw [mulBy, coeff_one_subst1 linv h0, Pts.coeff_one_linv h, PowerSeries.coeff_C_mul, h.2.1, one_mul,
    mul_one]

theorem subst_mulBy_mulBy {l linv : PowerSeries K} (h : IsLogPair l linv) (a b : K) :
    PowerSeries.subst (mulBy l linv a) (mulBy l linv b) = mulBy l linv (b * a) := by
  rw [← Pts.fmul_eq_subst_mulBy h b (Pts.constantCoeff_mulBy h a), Pts.mulBy_eq_fmul a,
    Pts.fmul_fmul h b a PowerSeries.constantCoeff_X, ← Pts.mulBy_eq_fmul]

theorem mulBy_one {l linv : PowerSeries K} (h : IsLogPair l linv) :
    mulBy l linv 1 = PowerSeries.X := by
  rw [Pts.mulBy_eq_fmul, Pts.fmul_one h PowerSeries.constantCoeff_X]

theorem intPS_of_left_inverse (R : Subring K) {f g : PowerSeries K} (hf : IntPS R f)
    (hf0 : PowerSeries.constantCoeff f = 0) (hu : (PowerSeries.coeff 1 f)⁻¹ ∈ R)
    (hne : PowerSeries.coeff 1 f ≠ 0) (hg : PowerSeries.subst f g = PowerSeries.X) : IntPS R g := by

  let f' : PowerSeries R := PowerSeries.mk fun n => ⟨PowerSeries.coeff n f, hf n⟩
  have hmap : PowerSeries.map R.subtype f' = f := by
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    rfl
  have hf'0 : PowerSeries.constantCoeff f' = 0 := by
    apply Subtype.ext
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    simpa using hf0
  have hf'1 : IsUnit (PowerSeries.coeff 1 f') := by
    refine IsUnit.of_mul_eq_one ⟨(PowerSeries.coeff 1 f)⁻¹, hu⟩ ?_
    apply Subtype.ext
    rw [PowerSeries.coeff_mk]
    exact mul_inv_cancel₀ hne
  set t' : PowerSeries R := f'.substInvOfIsUnit hf'1 with ht'
  have ht'0 : PowerSeries.constantCoeff t' = 0 := PowerSeries.constantCoeff_substInvOfIsUnit f' hf'1
  have hr : PowerSeries.subst t' f' = PowerSeries.X :=
    PowerSeries.subst_substInvOfIsUnit_right f' hf'0 hf'1
  set t : PowerSeries K := PowerSeries.map R.subtype t' with ht
  have ht0 : PowerSeries.constantCoeff t = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ht, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, ht'0, map_zero]
  have hft : PowerSeries.subst t f = PowerSeries.X := by
    have := PowerSeries.map_subst (PowerSeries.HasSubst.substInvOfIsUnit f' hf'1)
      (h := R.subtype) f'
    rw [← ht', hr, hmap] at this
    rw [← PowerSeries.map_X R.subtype]
    exact this.symm
  have hgt : g = t := by
    have key := Pts.subst_subst hf0 ht0 g
    rw [hg, hft, PowerSeries.subst_X (JetSubstitutionLemmas.hs1 ht0), PowerSeries.X_subst] at key
    exact key.symm
  intro n
  rw [hgt, ht, PowerSeries.coeff_map]
  exact (PowerSeries.coeff n t').2

end SlopeTestRemainingChoices

theorem inverse_endo_integral_holds : InvEndInt := by
  intro K _ R l linv a h ha hai hE
  refine intPS_of_left_inverse R hE (Pts.constantCoeff_mulBy h a) ?_ ?_ ?_
  · rwa [coeff_one_mulBy h a]
  · rwa [coeff_one_mulBy h a]
  · rw [subst_mulBy_mulBy h, inv_mul_cancel₀ ha, mulBy_one h]

theorem adjoint_unit_norm_holds : AdjUnitNorm := by
  intro K _ _ R l linv ph a b N hFr hF1 ha hai hEa hEb hN hPh
  refine adjFromNorm K R l linv ph a b hFr ha hEa (inverse_endo_integral_holds K R l linv a hFr.1 ha hai hEa) hEb
    hPh ?_
  rw [hN]
  exact zLinInt K R l linv ph hFr hF1 N

theorem half_valuation_holds : HalfValuation := by
  intro K _ S c d hc hd hS
  have hdpos : 0 < ‖(d : K)‖ := norm_pos_iff.mpr hd
  have hcn : ‖c‖ ^ 2 = ‖(d : K)‖ := by rw [← norm_pow, hc, norm_neg]
  have hcpos : 0 < ‖c‖ := by
    rcases (norm_nonneg c).lt_or_eq with h | h
    · exact h
    · rw [← h] at hcn
      simp at hcn
      exact absurd hcn.symm (ne_of_gt hdpos)
  have hsq : ‖(d : K)‖ ^ (1 / 2 : ℝ) = ‖c‖ := by
    rw [← hcn, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg c)]
  rw [Real.rpow_neg hdpos.le, hsq]
  rw [norm_mul] at hS
  rw [← one_div, le_div_iff₀ hcpos, mul_comm]
  exact hS

theorem ramified_shape_holds : RamifiedShape := by
  intro K _ _ _ l linv ph a b d hFr hF1 hNeg h2 hAdj hab hd
  have hlp : IsLogPair l linv := hFr.1
  have h2i : (2 : K)⁻¹ ∈ unitBall K := by
    show ‖(2 : K)⁻¹‖ ≤ 1
    rw [norm_inv, h2, inv_one]
  have hdK : (d : K) ≠ 0 := Nat.cast_ne_zero.mpr hd
  obtain ⟨⟨H, hH, hexp⟩, hS⟩ := jetsShape K (unitBall K) l linv ph hFr hF1 hNeg h2i
  have hl' : IsOneUnit (unitBall K) (PowerSeries.derivative K l) :=
    logDerivInt K (unitBall K) l linv hlp hFr.2.1
  refine ⟨half_valuation_holds K _ (a - b) d hab hdK (hS a b hAdj), ?_, ?_⟩
  · intro i hi hi2
    rcases Nat.lt_or_ge i 3 with h3 | h3
    · have : i = 1 := by omega
      subst this
      exact jetOne K (unitBall K) l linv ph hlp hl' hFr.2.2 hNeg h2i
    · exact (derivation_cube_integral_jet K (unitBall K) l linv ph hFr hF1).2 i h3
  · have hs : PowerSeries.HasSubst linv := JetSubstitutionLemmas.hs1 hlp.2.2.1
    set c : K := jet l ph 2 / 2 with hc
    have hq0 : PowerSeries.constantCoeff (-(PowerSeries.C c * l ^ 2)) = 0 := by
      rw [map_neg, map_mul, map_pow, hlp.1]
      simp
    have hq0' : PowerSeries.constantCoeff (-(PowerSeries.C c * PowerSeries.X ^ 2) : PowerSeries K) = 0 := by
      simp
    have hph0 : PowerSeries.constantCoeff (-ph) = 0 := by rw [map_neg, hFr.2.2, neg_zero]
    have hsub : PowerSeries.subst linv (-(PowerSeries.C c * l ^ 2)) =
        (-(PowerSeries.C c * PowerSeries.X ^ 2) : PowerSeries K) := by
      rw [← PowerSeries.coe_substAlgHom hs, map_neg, map_mul, map_pow, PowerSeries.coe_substAlgHom hs,
        PowerSeries.subst_C, hlp.2.2.2.2]
      rfl
    have hid : PowerSeries.subst linv (mvExp (-ph) : PowerSeries K) =
        (mvExp (-(PowerSeries.C c * PowerSeries.X ^ 2)) : PowerSeries K) * PowerSeries.subst linv H := by
      rw [hexp, PowerSeries.subst_mul hs, mvExpSubst K Unit _ linv hq0 hlp.2.2.1, hsub]
    refine ⟨PowerSeries.subst linv H, (jets_of_dist_jets_holds K (unitBall K) l linv H hlp).1 hH, ?_, hid⟩
    have hcc := congrArg PowerSeries.constantCoeff hid
    rw [map_mul, JetSubstitutionLemmas.cc_subst1 hlp.2.2.1] at hcc
    have e1 : PowerSeries.constantCoeff (mvExp (-ph) : PowerSeries K) = 1 :=
      (mvExpLaws K Unit).2.1 _ hph0
    have e2 : PowerSeries.constantCoeff
        (mvExp (-(PowerSeries.C c * PowerSeries.X ^ 2)) : PowerSeries K) = 1 :=
      (mvExpLaws K Unit).2.1 _ hq0'
    rw [e1, e2, one_mul] at hcc
    exact hcc.symm

end Formalism.L2.Th1.G
