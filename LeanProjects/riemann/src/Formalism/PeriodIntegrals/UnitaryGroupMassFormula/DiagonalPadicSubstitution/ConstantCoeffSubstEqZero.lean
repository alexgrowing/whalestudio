import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.SubstOps

noncomputable section

open Classical

namespace PI.BeDiagZp.ContPf

variable {p : ℕ} [Fact p.Prime]

def CC {σ : Type} (G : ℂ_[p] → MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, Continuous fun c => MvPowerSeries.coeff n (G c)

theorem cc_const {σ : Type} (F : MvPowerSeries σ ℂ_[p]) : CC fun _ : ℂ_[p] => F :=
  fun _ => continuous_const

theorem cc_C {σ : Type} : CC fun c : ℂ_[p] => (MvPowerSeries.C c : MvPowerSeries σ ℂ_[p]) := by
  intro n
  simp only [MvPowerSeries.coeff_C]
  by_cases h : n = 0
  · simp only [h, if_true]; exact continuous_id
  · simp only [h, if_false]; exact continuous_const

theorem cc_add {σ : Type} {F G : ℂ_[p] → MvPowerSeries σ ℂ_[p]} (hF : CC F) (hG : CC G) :
    CC fun c => F c + G c := by
  intro n; simp only [map_add]; exact (hF n).add (hG n)

theorem cc_sub {σ : Type} {F G : ℂ_[p] → MvPowerSeries σ ℂ_[p]} (hF : CC F) (hG : CC G) :
    CC fun c => F c - G c := by
  intro n; simp only [map_sub]; exact (hF n).sub (hG n)

theorem cc_mul {σ : Type} {F G : ℂ_[p] → MvPowerSeries σ ℂ_[p]} (hF : CC F) (hG : CC G) :
    CC fun c => F c * G c := by
  intro n
  simp only [MvPowerSeries.coeff_mul]
  exact continuous_finsetSum _ fun x _ => (hF x.1).mul (hG x.2)

theorem cc_pow {σ : Type} {F : ℂ_[p] → MvPowerSeries σ ℂ_[p]} (hF : CC F) (k : ℕ) :
    CC fun c => F c ^ k := by
  induction k with
  | zero => simp only [pow_zero]; exact cc_const 1
  | succ k ih => simp only [pow_succ]; exact cc_mul ih hF

theorem coeff_pow_eq_zero {σ : Type} (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (e : σ →₀ ℕ) (d : ℕ) (h : e.degree < d) : MvPowerSeries.coeff e (a ^ d) = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast h) (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero d ha)

theorem coeff_subst_eq_sum {σ : Type} (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (F : PowerSeries ℂ_[p]) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff e (PowerSeries.subst a F) =
      ∑ d ∈ Finset.range (e.degree + 1), PowerSeries.coeff d F • MvPowerSeries.coeff e (a ^ d) := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hlt
  apply hd
  simp only [coeff_pow_eq_zero a ha e d (by omega), smul_zero]

theorem cc_subst {σ : Type} (F : PowerSeries ℂ_[p]) {G : ℂ_[p] → MvPowerSeries σ ℂ_[p]}
    (h0 : ∀ c, MvPowerSeries.constantCoeff (G c) = 0) (hG : CC G) :
    CC fun c => PowerSeries.subst (G c) F := by
  intro e
  simp only [coeff_subst_eq_sum _ (h0 _)]
  exact continuous_finsetSum _ fun d _ => by
    have h : Continuous fun c => MvPowerSeries.coeff e (G c ^ d) := cc_pow hG d e
    exact h.const_smul (PowerSeries.coeff d F)

theorem cc_expMv {σ : Type} {G : ℂ_[p] → MvPowerSeries σ ℂ_[p]} (hG : CC G) :
    CC fun c => expMv (G c) := by
  intro e
  show Continuous fun c => ∑ n ∈ Finset.range ((e.sum fun _ k => k) + 1),
    MvPowerSeries.coeff e (G c ^ n) / (n.factorial : ℂ_[p])
  exact continuous_finsetSum _ fun n _ => (cc_pow hG n e).div_const _

theorem constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution {σ : Type} (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (F : PowerSeries ℂ_[p]) (hF : PowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a F) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero ha F hF

theorem zc_continuous : Continuous (zc : ℤ_[p] → ℂ_[p]) := by
  unfold zc
  exact (continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val

theorem zc_natCast (n : ℕ) : zc (n : ℤ_[p]) = (n : ℂ_[p]) := by
  simp [zc]

end PI.BeDiagZp.ContPf

namespace PI.BeDiagZp

open ContPf

theorem cont_holds : Cont := by
  intro p _ l ex ph hex hl hN n
  let u : MvPowerSeries Unit ℂ_[p] := Xv ()
  have hu : MvPowerSeries.constantCoeff u = 0 := by simp [u, Xv]
  have hlu : MvPowerSeries.constantCoeff (PowerSeries.subst u l) = 0 := constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution u hu l hl
  have hM0 : ∀ c : ℂ_[p], MvPowerSeries.constantCoeff (mulBy l ex c u) = 0 := by
    intro c
    apply constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution _ _ ex hex
    simp [hlu]
  have hM : CC fun c : ℂ_[p] => mulBy l ex c u := by
    apply cc_subst ex (fun c => by simp [hlu]) (cc_mul cc_C (cc_const _))
  have hA0 : ∀ c : ℂ_[p], MvPowerSeries.constantCoeff (add l ex u (mulBy l ex c u)) = 0 := by
    intro c
    apply constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution _ _ ex hex
    simp [hlu, constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution _ (hM0 c) l hl]
  have hA : CC fun c : ℂ_[p] => add l ex u (mulBy l ex c u) := by
    apply cc_subst ex (fun c => by simp [hlu, constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution _ (hM0 c) l hl])
    exact cc_add (cc_const _) (cc_subst l hM0 hM)
  have hB : CC fun c : ℂ_[p] => be l ex ph u (mulBy l ex c u) := by
    unfold be phAt
    exact cc_sub (cc_sub (cc_subst ph hA0 hA) (cc_const _)) (cc_subst ph hM0 hM)
  have hF : CC fun c : ℂ_[p] =>
      be l ex ph u (mulBy l ex c u) - MvPowerSeries.C c * be l ex ph u u :=
    cc_sub hB (cc_mul cc_C (cc_const _))
  have hE := cc_expMv hF
  have hcl : IsClosed {c : ℂ_[p] | Simeq (be l ex ph u (mulBy l ex c u))
      (MvPowerSeries.C c * be l ex ph u u)} := by
    simp only [Simeq, IntegralMv, IsIntP, Set.ofPred_and, Set.ofPred_forall]
    refine IsClosed.inter (isClosed_eq ?_ continuous_const)
      (isClosed_iInter fun α => isClosed_le (continuous_norm.comp (hE α)) continuous_const)
    exact (hF 0).congr fun c => MvPowerSeries.coeff_zero_eq_constantCoeff_apply _
  have hcl' := hcl.preimage zc_continuous
  refine PadicInt.denseRange_natCast.induction_on n hcl' ?_
  intro k
  show Simeq _ _
  rw [zc_natCast]
  exact hN k

end PI.BeDiagZp
