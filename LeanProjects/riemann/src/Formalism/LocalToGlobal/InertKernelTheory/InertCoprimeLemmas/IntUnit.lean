import Formalism.LocalToGlobal.InertKernelTheory.DefsMMInv
import Formalism.LocalToGlobal.InertKernelTheory.DefsBasis
import Formalism.LocalToGlobal.InertKernelTheory.StatementCc
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.CurveIdealPrimeReduction
import Formalism.LocalToGlobal.InertKernelTheory.StatementModel
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntBasis
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FormalExponentialAgree
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.FirstGeometricConditionOfProperties
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupCommon.ExpLog

noncomputable section

namespace Formalism.L2.KerInert.IntegralUnitSubstitution

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.MainNotions.Ext Formalism.MainNotions.Ext.CutA

variable {p : ℕ} [Fact p.Prime]

theorem expMv_pi {σ : Type} (F : MvPowerSeries σ ℂ_[p]) : Formalism.MainNotions.TaylorLogMetric.expMv F = PI.FglPhSplit.expMv F := rfl

theorem expMv_subst_eq {σ : Type} {F : MvPowerSeries σ ℂ_[p]} (hF : MvPowerSeries.constantCoeff F = 0) :
    Formalism.MainNotions.TaylorLogMetric.expMv F = PowerSeries.subst F (PowerSeries.exp ℂ_[p]) := by
  rw [expMv_pi]; exact PI.FglPhSplit.Wk.expMv_eq_subst hF

theorem cc_expMv {σ : Type} {F : MvPowerSeries σ ℂ_[p]} (hF : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (Formalism.MainNotions.TaylorLogMetric.expMv F) = 1 := by
  rw [expMv_subst_eq hF, PI.FglShared.constantCoeff_subst_of_zero hF]
  simp

theorem expMv_zero' {σ : Type} : Formalism.MainNotions.TaylorLogMetric.expMv (0 : MvPowerSeries σ ℂ_[p]) = 1 := by
  rw [expMv_subst_eq (map_zero _)]
  simp [PowerSeries.subst_zero_eq_C_constantCoeff]

theorem expMv_add'' {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) :
    Formalism.MainNotions.TaylorLogMetric.expMv (f + g) = Formalism.MainNotions.TaylorLogMetric.expMv f * Formalism.MainNotions.TaylorLogMetric.expMv g :=
  PI.FglShared.expMv_add' hf hg

theorem expMv_sum {σ ι : Type} (s : Finset ι) (f : ι → MvPowerSeries σ ℂ_[p])
    (hf : ∀ i, MvPowerSeries.constantCoeff (f i) = 0) :
    Formalism.MainNotions.TaylorLogMetric.expMv (∑ i ∈ s, f i) = ∏ i ∈ s, Formalism.MainNotions.TaylorLogMetric.expMv (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using (expMv_zero' (σ := σ) (p := p))
  · intro a s ha ih
    have h0 : MvPowerSeries.constantCoeff (∑ i ∈ s, f i) = 0 := by
      rw [map_sum]; exact Finset.sum_eq_zero fun i _ => hf i
    rw [Finset.sum_insert ha, Finset.prod_insert ha, expMv_add'' (hf a) h0, ih]

theorem msubst_psubst {τ υ : Type} {a : MvPowerSeries τ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    {b : τ → MvPowerSeries υ ℂ_[p]} (hb : MvPowerSeries.HasSubst b) (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst b (PowerSeries.subst a f) = PowerSeries.subst (MvPowerSeries.subst b a) f := by
  have h1 : MvPowerSeries.HasSubst (fun _ : Unit => a) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => ha)
  exact MvPowerSeries.subst_comp_subst_apply h1 hb f

theorem subst_expMv {σ τ : Type} {b : σ → MvPowerSeries τ ℂ_[p]} (hb : MvPowerSeries.HasSubst b)
    {F : MvPowerSeries σ ℂ_[p]} (hF : MvPowerSeries.constantCoeff F = 0)
    (hb0 : MvPowerSeries.constantCoeff (MvPowerSeries.subst b F) = 0) :
    MvPowerSeries.subst b (Formalism.MainNotions.TaylorLogMetric.expMv F) = Formalism.MainNotions.TaylorLogMetric.expMv (MvPowerSeries.subst b F) := by
  rw [expMv_subst_eq hF, expMv_subst_eq hb0, msubst_psubst hF hb]

section G
variable (g : G1 p)

theorem cc_l : PowerSeries.constantCoeff g.l = 0 := by
  unfold G1.l flog
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  simp

theorem cc_lg {σ : Type} {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (g.lg a) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero ha _ (cc_l g)

theorem cc_pt (hOk : g.Ok) {σ : Type} {y : MvPowerSeries σ ℂ_[p]} (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.constantCoeff (g.pt y) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hy _ hOk.2.2.1

theorem lg_pt (hOk : g.Ok) {σ : Type} {y : MvPowerSeries σ ℂ_[p]} (hy : MvPowerSeries.constantCoeff y = 0) :
    g.lg (g.pt y) = y := by
  unfold G1.lg G1.pt
  rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hOk.2.2.1)
    (PowerSeries.HasSubst.of_constantCoeff_zero hy), hOk.2.2.2, PowerSeries.subst_X
    (PowerSeries.HasSubst.of_constantCoeff_zero hy)]

theorem subst_lg {σ τ : Type} {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    {b : σ → MvPowerSeries τ ℂ_[p]} (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (g.lg a) = g.lg (MvPowerSeries.subst b a) :=
  msubst_psubst ha hb _

theorem add_eq_subst (hOk : g.Ok) {σ : Type} {a b : MvPowerSeries σ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) :
    g.add a b = MvPowerSeries.subst ![a, b] (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) := by
  have hs : MvPowerSeries.HasSubst ![a, b] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simpa)
  have hX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := fun i => by simp
  have h0 : MvPowerSeries.constantCoeff (g.lg (Xv 0) + g.lg (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [map_add, cc_lg g (hX 0), cc_lg g (hX 1), add_zero]
  unfold G1.add G1.pt
  rw [msubst_psubst h0 hs, ← MvPowerSeries.coe_substAlgHom hs, map_add, MvPowerSeries.coe_substAlgHom hs,
    subst_lg g (hX 0) hs, subst_lg g (hX 1) hs, MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs]
  rfl

theorem mulBy_eq_subst {σ : Type} (c : ℂ_[p]) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    g.mulBy c a = MvPowerSeries.subst (fun _ : Unit => a) (g.mulBy c (Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
  have hs : MvPowerSeries.HasSubst (fun _ : Unit => a) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => ha)
  have hX : MvPowerSeries.constantCoeff (Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := by simp
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.C c * g.lg (Xv ()) : MvPowerSeries Unit ℂ_[p]) = 0 := by
    rw [map_mul, cc_lg g hX, mul_zero]
  unfold G1.mulBy G1.pt
  rw [msubst_psubst h0 hs, ← MvPowerSeries.coe_substAlgHom hs, map_mul, MvPowerSeries.coe_substAlgHom hs,
    MvPowerSeries.subst_C, subst_lg g hX hs, MvPowerSeries.subst_X hs]

theorem integral_zero {σ : Type} : IntegralMv (0 : MvPowerSeries σ ℂ_[p]) := fun n => by
  simp [IsIntP]

theorem lin_partial (hOk : g.Ok) {r : ℕ} (c : Fin r → ℂ_[p])
    (hc : ∀ j, IntegralMv (g.mulBy (c j) (Xv ()) : MvPowerSeries Unit ℂ_[p]))
    (ha : IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])) (s : Finset (Fin r)) :
    MvPowerSeries.constantCoeff (g.pt (∑ j ∈ s, MvPowerSeries.C (c j) * g.lg (Xv j)) : MvPowerSeries (Fin r) ℂ_[p]) = 0 ∧
      IntegralMv (g.pt (∑ j ∈ s, MvPowerSeries.C (c j) * g.lg (Xv j)) : MvPowerSeries (Fin r) ℂ_[p]) := by
  classical
  have hX : ∀ j : Fin r, MvPowerSeries.constantCoeff (Xv j : MvPowerSeries (Fin r) ℂ_[p]) = 0 := fun j => by simp
  have hT : ∀ t : Finset (Fin r),
      MvPowerSeries.constantCoeff (∑ j ∈ t, MvPowerSeries.C (c j) * g.lg (Xv j) : MvPowerSeries (Fin r) ℂ_[p]) = 0 := by
    intro t
    rw [map_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [map_mul, cc_lg g (hX j), mul_zero]
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty]
    unfold G1.pt
    rw [PowerSeries.subst_zero_of_constantCoeff_zero hOk.2.2.1]
    exact ⟨map_zero _, integral_zero⟩
  · intro j t hj ih
    have hm0 : MvPowerSeries.constantCoeff (g.mulBy (c j) (Xv j) : MvPowerSeries (Fin r) ℂ_[p]) = 0 := by
      unfold G1.mulBy
      exact cc_pt g hOk (by rw [map_mul, cc_lg g (hX j), mul_zero])
    have hmI : IntegralMv (g.mulBy (c j) (Xv j) : MvPowerSeries (Fin r) ℂ_[p]) := by
      rw [mulBy_eq_subst g (c j) (hX j)]
      exact IntegralOrthonormalChange.integral_subst _ (fun _ => hX j) (fun _ => fun n => by
        rw [MvPowerSeries.coeff_X]; split_ifs <;> simp [IsIntP]) (hc j)
    have e : (∑ j' ∈ insert j t, MvPowerSeries.C (c j') * g.lg (Xv j') : MvPowerSeries (Fin r) ℂ_[p]) =
        g.lg (g.mulBy (c j) (Xv j)) + g.lg (g.pt (∑ j' ∈ t, MvPowerSeries.C (c j') * g.lg (Xv j'))) := by
      rw [Finset.sum_insert hj, lg_pt g hOk (hT t)]
      unfold G1.mulBy
      rw [lg_pt g hOk (by rw [map_mul, cc_lg g (hX j), mul_zero])]
    rw [e]
    refine ⟨cc_pt g hOk (by rw [map_add, cc_lg g hm0, cc_lg g ih.1, add_zero]), ?_⟩
    change IntegralMv (g.add _ _)
    rw [add_eq_subst g hOk hm0 ih.1]
    exact IntegralOrthonormalChange.integral_subst _ (fun i => by fin_cases i <;> simp [hm0, ih.1])
      (fun i => by fin_cases i <;> simp [hmI, ih.2]) ha

theorem lin_cc_int (hOk : g.Ok) {r : ℕ} (c : Fin r → ℂ_[p])
    (hc : ∀ j, IntegralMv (g.mulBy (c j) (Xv ()) : MvPowerSeries Unit ℂ_[p]))
    (ha : IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])) :
    MvPowerSeries.constantCoeff (g.lin c (fun j => Xv j) : MvPowerSeries (Fin r) ℂ_[p]) = 0 ∧
      IntegralMv (g.lin c (fun j => Xv j) : MvPowerSeries (Fin r) ℂ_[p]) :=
  lin_partial g hOk c hc ha Finset.univ

theorem lg_lin (hOk : g.Ok) {r : ℕ} (c : Fin r → ℂ_[p]) :
    g.lg (g.lin c (fun j => Xv j) : MvPowerSeries (Fin r) ℂ_[p]) =
      ∑ j, MvPowerSeries.C (c j) * g.lg (Xv j : MvPowerSeries (Fin r) ℂ_[p]) := by
  unfold G1.lin
  refine lg_pt g hOk ?_
  rw [map_sum]
  exact Finset.sum_eq_zero fun j _ => by rw [map_mul, cc_lg g (by simp), mul_zero]

theorem inv_ePhi1 (he1 : PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1) {σ : Type}
    {y : MvPowerSeries σ ℂ_[p]} (hy : MvPowerSeries.constantCoeff y = 0) :
    (PowerSeries.subst y (ePhi1 g.lam g.abelian₂ g.C g.wq))⁻¹ = Formalism.MainNotions.TaylorLogMetric.expMv (g.phAt y) := by
  set e := ePhi1 g.lam g.abelian₂ g.C g.wq with he
  have hE : PI.FglPhSplit.expMv (PI.FglShared.logS e) = e := PI.FglShared.expMv_logS he1
  have hph : g.ph = -PI.FglShared.logS e := by
    show -logMv e = _
    rfl
  have hl0 : MvPowerSeries.constantCoeff (PI.FglShared.logS e) = 0 := PI.FglShared.constantCoeff_logS e
  have hsy : PowerSeries.HasSubst y := PowerSeries.HasSubst.of_constantCoeff_zero hy
  have hphy0 : MvPowerSeries.constantCoeff (g.phAt y) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hy _ (ph0 g)
  have h1 : PowerSeries.subst y e = Formalism.MainNotions.TaylorLogMetric.expMv (-(g.phAt y)) := by
    conv_lhs => rw [← hE]
    rw [← PI.FglShared.expMv_subst' hy hl0, expMv_pi]
    congr 1
    unfold G1.phAt
    rw [hph, ← PowerSeries.coe_substAlgHom hsy, map_neg, neg_neg]
  have hn0 : MvPowerSeries.constantCoeff (-(g.phAt y)) = 0 := by rw [map_neg, hphy0, neg_zero]
  have hne : MvPowerSeries.constantCoeff (Formalism.MainNotions.TaylorLogMetric.expMv (-(g.phAt y))) ≠ 0 := by
    rw [cc_expMv hn0]; exact one_ne_zero
  rw [h1]
  symm
  rw [MvPowerSeries.eq_inv_iff_mul_eq_one hne, ← expMv_add'' hphy0 hn0, add_neg_cancel, expMv_zero']

theorem ePh_eq (he1 : PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1) (hp : p ≠ 2) (r : ℕ) :
    ePh g.lam g.abelian₂ g.C g.wq r = Formalism.MainNotions.TaylorLogMetric.expMv (∑ i : Fin r, g.phAt (Xv i)) := by
  unfold ePh
  rw [if_neg hp, expMv_sum Finset.univ (fun i : Fin r => (g.phAt (Xv i) : MvPowerSeries (Fin r) ℂ_[p]))
    (fun i => PowerSeries.constantCoeff_subst_eq_zero (by simp) _ (ph0 g))]
  exact Finset.prod_congr rfl fun i _ => inv_ePhi1 g he1 (by simp)

end G

theorem core (D : D7) (g : G1 p) (hOk : g.Ok) (hp : p ≠ 2)
    (he : ∀ α ∈ OKp D g.lam, IntegralMv (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p]))
    (ha : IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
    (hOK : ∀ a : 𝓞 D.host.K, Nat.Coprime (Algebra.norm ℤ a).natAbs p →
      Simeq (g.phAt (g.mulBy (tauK D g.lam (a : D.host.K)) (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (tauK D g.lam (a : D.host.K) * tauKc D g.lam (a : D.host.K)) * g.phAt (Xv ())))
    (hB : Simeq (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)))
    (he1 : PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1)
    (r : ℕ) (M : Fin r → Fin r → ℂ_[p] × ℂ_[p]) (hM : ∀ i j, M i j ∈ OKp D g.lam)
    (hu : ∀ j j', ∑ i, M i j * (M i j').swap = if j = j' then 1 else 0) :
    ∃ S : Fin r → MvPowerSeries (Fin r) ℂ_[p],
      (∀ i, MvPowerSeries.constantCoeff (S i) = 0) ∧ (∀ i, IntegralMv (S i)) ∧
      (∀ i, PowerSeries.subst (S i) g.l =
        ∑ j, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) (M i j).1 *
          PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin r) ℂ_[p]) g.l) ∧
      ∃ V : MvPowerSeries (Fin r) ℂ_[p], IntegralMv V ∧
        ePh g.lam g.abelian₂ g.C g.wq r = MvPowerSeries.subst S (ePh g.lam g.abelian₂ g.C g.wq r) * V := by
  classical

  have hn : ∀ α ∈ OKp D g.lam, Simeq (g.phAt (g.mulBy α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (α.1 * α.2) * g.phAt (Xv ())) := by
    refine phNormOfUnits_holds p g (OKp D g.lam) hOk hp (okpTwo_holds D p g.lam) (okpSwap_holds D p g.lam)
      (fun α hα β hβ => okp_add D g.lam α β hα hβ) (fun α hα β hβ => okp_mul D g.lam α β hα hβ)
      he ha ((okpTrace_holds D) p g.lam) ((okpNorm_holds D) p g.lam) ((okpTwoUnits2_holds D) p g.lam hp) hB ?_
    intro α hα h1 h2
    have hc := (okpUnitsDense_holds D) p g.lam hp α hα h1 h2
    refine phNormClosed_holds p g _ hOk ?_ ?_ α hc
    · rintro _ ⟨a, -, rfl⟩
      exact he _ (subset_closure ⟨a, rfl⟩)
    · rintro _ ⟨a, hcop, rfl⟩
      exact hOK a hcop
  have hb := beConjOfNorm_holds p g (OKp D g.lam) hOk (okpSwap_holds D p g.lam)
    (fun α hα β hβ => okp_add D g.lam α β hα hβ) he ha ((okpNorm_holds D) p g.lam)
    ((okpTwoUnits_holds D) p g.lam hp) hn hB
  let de : Fin r → Fin r → ℂ_[p] × ℂ_[p] := fun j i => M i j
  have hG := phGramG_holds p g (OKp D g.lam) hOk (okpSwap_holds D p g.lam) he ha hn hb hB (Fin r) r de
    (fun j i => hM i j)
  rw [gramUnitEq_holds p g hOk r de (fun j j' => hu j j')] at hG

  let S : Fin r → MvPowerSeries (Fin r) ℂ_[p] := fun i => g.lin (fun j => (M i j).1) (fun j => Xv j)
  have hSI : ∀ i, MvPowerSeries.constantCoeff (S i) = 0 ∧ IntegralMv (S i) := fun i =>
    lin_cc_int g hOk (fun j => (M i j).1) (fun j => he _ (hM i j)) ha
  have hS : MvPowerSeries.HasSubst S := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => (hSI i).1)
  refine ⟨S, fun i => (hSI i).1, fun i => (hSI i).2, fun i => ?_, ?_⟩
  · exact lg_lin g hOk (fun j => (M i j).1)
  ·
    have hPh : g.PhOn de = ∑ i : Fin r, g.phAt (S i) := rfl
    have hX0 : ∀ i : Fin r, MvPowerSeries.constantCoeff (Xv i : MvPowerSeries (Fin r) ℂ_[p]) = 0 := fun i => by simp
    have hsum0 : MvPowerSeries.constantCoeff (∑ i : Fin r, g.phAt (Xv i) : MvPowerSeries (Fin r) ℂ_[p]) = 0 := by
      rw [map_sum]; exact Finset.sum_eq_zero fun i _ => PowerSeries.constantCoeff_subst_eq_zero (hX0 i) _ (ph0 g)
    have hsumS : MvPowerSeries.subst S (∑ i : Fin r, g.phAt (Xv i) : MvPowerSeries (Fin r) ℂ_[p]) =
        ∑ i : Fin r, g.phAt (S i) := by
      rw [← MvPowerSeries.coe_substAlgHom hS, map_sum, MvPowerSeries.coe_substAlgHom hS]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold G1.phAt
      rw [msubst_psubst (hX0 i) hS, MvPowerSeries.subst_X hS]
    have hS0 : MvPowerSeries.constantCoeff (∑ i : Fin r, g.phAt (S i) : MvPowerSeries (Fin r) ℂ_[p]) = 0 := by
      rw [map_sum]; exact Finset.sum_eq_zero fun i _ => PowerSeries.constantCoeff_subst_eq_zero (hSI i).1 _ (ph0 g)
    obtain ⟨hG0, hGI⟩ := hG
    rw [hPh] at hG0 hGI
    have hd0 : MvPowerSeries.constantCoeff (∑ i : Fin r, g.phAt (Xv i) - ∑ i : Fin r, g.phAt (S i) :
        MvPowerSeries (Fin r) ℂ_[p]) = 0 := by rw [map_sub, hsum0, hS0, sub_zero]
    refine ⟨Formalism.MainNotions.TaylorLogMetric.expMv (∑ i : Fin r, g.phAt (Xv i) - ∑ i : Fin r, g.phAt (S i)), ?_, ?_⟩
    ·
      have hmul : Formalism.MainNotions.TaylorLogMetric.expMv (∑ i : Fin r, g.phAt (Xv i) - ∑ i : Fin r, g.phAt (S i)) *
          Formalism.MainNotions.TaylorLogMetric.expMv (∑ i : Fin r, g.phAt (S i) - ∑ i : Fin r, g.phAt (Xv i)) = 1 := by
        rw [← expMv_add'' hd0 hG0]
        rw [show (∑ i : Fin r, g.phAt (Xv i) - ∑ i : Fin r, g.phAt (S i)) +
            (∑ i : Fin r, g.phAt (S i) - ∑ i : Fin r, g.phAt (Xv i)) = (0 : MvPowerSeries (Fin r) ℂ_[p]) by ring]
        exact expMv_zero'
      exact PI.FglShared.int_of_mul_eq_one (fun α => hGI α) (cc_expMv hG0) hmul
    · rw [ePh_eq g he1 hp r, subst_expMv hS hsum0 (by rw [hsumS]; exact hS0), hsumS,
        ← expMv_add'' hS0 hd0]
      congr 1
      ring

theorem unitSubstLoc_of (hC : CcPrime) (hE : EndIntInertAll) (hN : PhNormOKInertAll) (hB : BiaddInertAll) :
    UnitSubstLoc := by
  intro D cc δ hcI hδ p _ hp5 hjac lam C wq hM hW r M hMO hMu
  obtain ⟨cc', δ', hcI', hδ', hcop, hL⟩ := hC D cc δ hcI hδ p hjac
  have hp : p ≠ 2 := by omega
  have hl0 : PowerSeries.constantCoeff (flog (C • wModel lam (lamOf D cc δ)) wq) = 0 := by
    unfold flog
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    simp
  have hl1 : PowerSeries.coeff 1 (flog (C • wModel lam (lamOf D cc δ)) wq) = 1 := by
    rw [Dict.formal_logarithm_agree p _ wq hW]
    exact (Formalism.L2.Th1.A.logSpec ℂ_[p] (C • wModel lam (lamOf D cc δ))).2.1
  have hu : IsUnit (PowerSeries.coeff 1 (flog (C • wModel lam (lamOf D cc δ)) wq)) := by
    rw [hl1]; exact isUnit_one
  let g : G1 p := ⟨lam, lamOf D cc δ, C, wq,
    (flog (C • wModel lam (lamOf D cc δ)) wq).substInvOfIsUnit hu⟩
  have hOk : g.Ok := ⟨Formalism.MainNotions.GL3Theta.IsModel.toU hM, hW, PowerSeries.constantCoeff_substInvOfIsUnit _ hu,
    PowerSeries.subst_substInvOfIsUnit_right _ hl0 hu⟩
  have hA : At D cc' δ' g := ⟨hcI', hcop, hδ', hL, hOk⟩
  exact core D g hOk hp (hE D p cc' δ' g hA hp5 hjac) (addInt_holds D p cc' δ' g hA).1
    (hN D p cc' δ' g hA hp5 hjac) (hB D p cc' δ' g hA hp5 hjac).1 (ePhiOne_holds D p cc' δ' g hA) r M hMO hMu

end Formalism.L2.KerInert.IntegralUnitSubstitution

namespace Formalism.L2.KerInert

theorem unitSubstLoc_of (hC : CcPrime) (hE : EndIntInertAll) (hN : PhNormOKInertAll) (hB : BiaddInertAll) :
    UnitSubstLoc :=
  IntegralUnitSubstitution.unitSubstLoc_of hC hE hN hB

theorem unitSubstLoc_of_model (hE : EndIntInertAll) (hN : PhNormOKInertAll) (hB : BiaddInertAll) : UnitSubstLoc :=
  unitSubstLoc_of curve_ideal_prime hE hN hB

end Formalism.L2.KerInert
