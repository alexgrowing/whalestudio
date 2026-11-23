import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BiadditivePadicLinear.Cont2
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.ConstantCoeffSubstEqZero

noncomputable section

open Classical

namespace PI.BiaddZpLinW

open PI.BiaddZpLin PI.BeDiagZp.ContPf

section SlopeTestRemainingChoices

variable {p : ℕ} [Fact p.Prime]

theorem cc_expMv' {σ : Type} {G : ℂ_[p] → MvPowerSeries σ ℂ_[p]} (hG : CC G) :
    CC fun c => expMv (G c) := by
  intro e
  show Continuous fun c => ∑ n ∈ Finset.range ((e.sum fun _ k => k) + 1),
    MvPowerSeries.coeff e (G c ^ n) / (n.factorial : ℂ_[p])
  exact continuous_finsetSum _ fun n _ => (cc_pow hG n e).div_const _

theorem zc_continuous' : Continuous (zc : ℤ_[p] → ℂ_[p]) := by
  unfold zc
  exact (continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val

theorem zc_natCast' (n : ℕ) : zc (n : ℤ_[p]) = (n : ℂ_[p]) := by
  simp [zc]

end SlopeTestRemainingChoices

theorem biadditive_continuous_padic : Cont2 := by
  intro p _ l ex ph hex hl hN n
  let a : MvPowerSeries (Fin 2) ℂ_[p] := Xv 0
  let b : MvPowerSeries (Fin 2) ℂ_[p] := Xv 1
  have ha : MvPowerSeries.constantCoeff a = 0 := by simp [a, Xv]
  have hb : MvPowerSeries.constantCoeff b = 0 := by simp [b, Xv]
  have hla : MvPowerSeries.constantCoeff (PowerSeries.subst a l) = 0 := constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution a ha l hl
  have hlb : MvPowerSeries.constantCoeff (PowerSeries.subst b l) = 0 := constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution b hb l hl
  have hM0 : ∀ c : ℂ_[p], MvPowerSeries.constantCoeff (mulBy l ex c a) = 0 := by
    intro c
    apply constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution _ _ ex hex
    simp [hla]
  have hM : CC fun c : ℂ_[p] => mulBy l ex c a := by
    apply cc_subst ex (fun c => by simp [hla]) (cc_mul cc_C (cc_const _))
  have hI0 : ∀ c : ℂ_[p], MvPowerSeries.constantCoeff
      (PowerSeries.subst (mulBy l ex c a) l + PowerSeries.subst b l) = 0 := by
    intro c
    simp [hlb, constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution _ (hM0 c) l hl]
  have hA0 : ∀ c : ℂ_[p], MvPowerSeries.constantCoeff (add l ex (mulBy l ex c a) b) = 0 := by
    intro c
    exact constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution _ (hI0 c) ex hex
  have hA : CC fun c : ℂ_[p] => add l ex (mulBy l ex c a) b := by
    apply cc_subst ex hI0
    exact cc_add (cc_subst l hM0 hM) (cc_const _)
  have hB : CC fun c : ℂ_[p] => be l ex ph (mulBy l ex c a) b := by
    unfold be phAt
    exact cc_sub (cc_sub (cc_subst ph hA0 hA) (cc_subst ph hM0 hM)) (cc_const _)
  have hF : CC fun c : ℂ_[p] =>
      be l ex ph (mulBy l ex c a) b - MvPowerSeries.C c * be l ex ph a b :=
    cc_sub hB (cc_mul cc_C (cc_const _))
  have hE := cc_expMv' hF
  have hcl : IsClosed {c : ℂ_[p] | Simeq (be l ex ph (mulBy l ex c a) b)
      (MvPowerSeries.C c * be l ex ph a b)} := by
    simp only [Simeq, IntegralMv, IsIntP, Set.ofPred_and, Set.ofPred_forall]
    refine IsClosed.inter (isClosed_eq ?_ continuous_const)
      (isClosed_iInter fun α => isClosed_le (continuous_norm.comp (hE α)) continuous_const)
    exact (hF 0).congr fun c => MvPowerSeries.coeff_zero_eq_constantCoeff_apply _
  have hcl' := hcl.preimage zc_continuous'
  refine PadicInt.denseRange_natCast.induction_on n hcl' ?_
  intro k
  show Simeq _ _
  rw [zc_natCast']
  exact hN k

end PI.BiaddZpLinW
