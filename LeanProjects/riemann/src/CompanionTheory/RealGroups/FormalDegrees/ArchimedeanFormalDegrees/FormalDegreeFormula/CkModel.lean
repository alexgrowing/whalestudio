import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.FormalDegreeFormula.ModelFunctionsMultiply
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelTau
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace CompanionTheory.RgFd.CkM

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

variable {n : ℕ}

theorem blkMinor_diag_mul (ε : Fin n → Bool) (c : Fin n) (d : Fin n → ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    blkMinor ε c (diagonal d * X) =
      (∏ q ∈ univ.filter (fun q : Fin n => ε q = ε c ∧ q ≤ c), d q) * blkMinor ε c X := by
  unfold blkMinor
  have hx : (diagonal d * X).submatrix (fun q : {q : Fin n // ε q = ε c ∧ q ≤ c} => (q : Fin n))
      (fun q : {q : Fin n // ε q = ε c ∧ q ≤ c} => (q : Fin n)) =
      diagonal (fun q : {q : Fin n // ε q = ε c ∧ q ≤ c} => d q) *
        X.submatrix (fun q : {q : Fin n // ε q = ε c ∧ q ≤ c} => (q : Fin n))
          (fun q : {q : Fin n // ε q = ε c ∧ q ≤ c} => (q : Fin n)) := by
    ext r s
    simp [Matrix.diagonal_mul]
  rw [hx, det_mul, det_diagonal]
  congr 1
  exact (Finset.prod_subtype (univ.filter (fun q : Fin n => ε q = ε c ∧ q ≤ c)) (by simp) d).symm

theorem model_function_diag_mul (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) (d : Fin n → ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    f0 ε m (diagonal d * X) = (∏ a, d a ^ (m a).toNat) * f0 ε m X := by
  unfold f0
  simp_rw [blkMinor_diag_mul, mul_pow]
  rw [Finset.prod_mul_distrib]
  congr 1
  simp_rw [← Finset.prod_pow]
  rw [Finset.prod_comm' (s' := fun q => univ.filter (fun c : Fin n => ε q = ε c ∧ q ≤ c)) (t' := univ)
    (by intro c q; simp)]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  have h := hwmf_tele ε m _ q rfl
  have h2 : ((∑ c ∈ univ.filter (fun c : Fin n => ε q = ε c ∧ q ≤ c), (mexp ε m c).toNat : ℕ) : ℤ) = m q := by
    rw [Nat.cast_sum, ← h]
    exact Finset.sum_congr rfl fun c _ => Int.toNat_of_nonneg (mexp_nonneg ε hm c)
  omega

theorem vsp_diag {ε : Fin n → Bool} {m : Fin n → ℤ} (hm : NonnegDom ε m) {f : KG ε → ℂ} (hf : f ∈ Vsp ε m)
    (y : KG ε) (d : Fin n → ℂ) (hy : toMK y = diagonal d) (x : KG ε) :
    f (y * x) = (∏ a, d a ^ (m a).toNat) * f x := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨k, rfl⟩ := hg
    show f0K ε m (y * x * k) = _ * f0K ε m (x * k)
    unfold f0K
    rw [show toMK (y * x * k) = diagonal d * toMK (x * k) by
      rw [mul_assoc]; show toMK y * toMK (x * k) = _; rw [hy]]
    exact model_function_diag_mul ε hm d _
  | zero => simp
  | add f g _ _ hf hg => simp [Pi.add_apply, hf, hg, mul_add]
  | smul c f _ hf => simp [Pi.smul_apply, hf, smul_eq_mul]; ring

def ev (ε : Fin n → Bool) (m : Fin n → ℤ) : MV ε m →ₗ[ℂ] ℂ := (LinearMap.proj (1 : KG ε)).comp (mvFnL ε m)

theorem ev_apply {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) : ev ε m f = f.fn 1 := rfl

theorem cpart1_Eaa (ε : Fin n → Bool) (a : Fin n) : cpart1 ε (bdPart ε (single a a (1 : ℂ))) = 0 := by
  ext i j
  rw [cpart1_bdPart_apply]
  by_cases h : ε i = ε j
  · rw [if_pos h]
    simp only [single_apply]
    split_ifs <;> aesop
  · simp [h]

theorem cpart2_Eaa (ε : Fin n → Bool) (a : Fin n) :
    cpart2 ε (bdPart ε (single a a (1 : ℂ))) = (-Complex.I) • single a a (1 : ℂ) := by
  ext i j
  rw [cpart2_bdPart_apply]
  by_cases hi : i = a
  · subst hi
    by_cases hj : j = i
    · subst hj; simp [single_apply]; ring
    · simp [single_apply, hj, Ne.symm hj]
  · by_cases hj : j = a
    · subst hj; simp [single_apply, hi, Ne.symm hi]
    · simp [single_apply, hi, hj, Ne.symm hi, Ne.symm hj]

theorem exp_Eaa (a : Fin n) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • ((-Complex.I) • single a a (1 : ℂ))) =
      diagonal (fun c => if c = a then Complex.exp (-(Complex.I * t)) else 1) := by
  have e : (t : ℂ) • ((-Complex.I) • single a a (1 : ℂ)) =
      diagonal (fun c => if c = a then -(Complex.I * t) else 0) := by
    ext i j
    by_cases hi : i = a <;> by_cases hj : j = a
    · subst hi; subst hj; simp [diagonal_apply, single_apply]; ring
    · subst hi; simp [diagonal_apply, single_apply, Ne.symm hj]
    · subst hj; simp [diagonal_apply, single_apply, Ne.symm hi, hi]
    · simp [diagonal_apply, single_apply, hi, hj, Ne.symm hi, Ne.symm hj]
  rw [e, Matrix.exp_diagonal]
  congr 1
  funext c
  by_cases h : c = a <;> simp [h, ← Complex.exp_eq_exp_ℂ]

theorem ev_dTau_Eaa {ε : Fin n → Bool} {m : Fin n → ℤ} (hm : NonnegDom ε m) (a : Fin n) (f : MV ε m) :
    ev ε m (dTau ε m (single a a 1) f) = ((m a : ℤ) : ℂ) * ev ε m f := by
  rw [ev_apply, ev_apply, dTau_fn]
  unfold rdc
  rw [cpart1_Eaa, cpart2_Eaa]
  have hX : inK ε ((-Complex.I) • single a a (1 : ℂ)) := by
    rw [← cpart2_Eaa ε a]; exact inK_cpart2_bdPart ε _
  have hX0 : inK ε (0 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← cpart1_Eaa ε a]; exact inK_cpart1_bdPart ε _
  have h0 : ∀ t, kcurve ε (0 : Matrix (Fin n) (Fin n) ℂ) t = 1 := by
    intro t
    apply onep_KG_ext
    rw [(kcurve_spec ε hX0).2.1 t]
    simp
    rfl
  have hc : ∀ t : ℝ, f.fn (1 * kcurve ε ((-Complex.I) • single a a (1 : ℂ)) t) =
      Complex.exp (-(Complex.I * t)) ^ (m a).toNat * f.fn 1 := by
    intro t
    rw [← mul_one (1 * kcurve ε _ t), one_mul]
    rw [vsp_diag hm f.mem _ _ (by rw [(kcurve_spec ε hX).2.1 t, exp_Eaa]) 1]
    congr 1
    rw [Finset.prod_eq_single a (fun c _ hc => by simp [hc]) (by simp)]
    simp
  simp_rw [h0, mul_one, hc]
  rw [deriv_const, zero_add]
  have hd : HasDerivAt (fun t : ℝ => Complex.exp (-(Complex.I * t)) ^ (m a).toNat * f.fn 1)
      (((m a).toNat : ℂ) * (-Complex.I) * f.fn 1) 0 := by
    have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
    have h1 := (((h0.const_mul Complex.I).neg.cexp).pow (m a).toNat).mul_const (f.fn 1)
    refine h1.congr_deriv ?_
    simp
  rw [hd.deriv]
  have hma : (((m a).toNat : ℕ) : ℂ) = ((m a : ℤ) : ℂ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (hm.2 a)]
  rw [hma]
  linear_combination (-((m a : ℤ) : ℂ) * f.fn 1) * Complex.I_sq

theorem model_op {ε : Fin n → Bool} {m : Fin n → ℤ} (hm : NonnegDom ε m) (k : KG ε) :
    (modelKType ε hm).op k = tauC ε m k := rfl

theorem model_dτ {ε : Fin n → Bool} {m : Fin n → ℤ} (hm : NonnegDom ε m) :
    (modelKType ε hm).dτ = dTau ε m := rfl

theorem model_w {ε : Fin n → Bool} {m : Fin n → ℤ} (hm : NonnegDom ε m) : (modelKType ε hm).w = wN ε m := rfl

def uEv (ε : Fin n → Bool) (m : Fin n → ℤ) : MV ε m :=
  (InnerProductSpace.toDual ℂ (MV ε m)).symm (LinearMap.toContinuousLinearMap (ev ε m))

theorem inner_uEv {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) : ⟪uEv ε m, f⟫_ℂ = ev ε m f := by
  rw [uEv, InnerProductSpace.toDual_symm_apply]
  rfl

theorem uEv_wt {ε : Fin n → Bool} {m : Fin n → ℤ} (hm : NonnegDom ε m) (a : Fin n) :
    dTau ε m (single a a 1) (uEv ε m) = (((m a : ℤ) : ℝ) : ℂ) • uEv ε m := by
  refine ext_inner_right ℂ fun f => ?_
  have hU := KType.kUnit (modelKType ε hm) a a rfl (uEv ε m) f
  simp only [kunits, model_dτ, ContinuousLinearMap.coe_coe] at hU
  have hU' : ⟪dTau ε m (single a a 1) (uEv ε m), f⟫_ℂ = ⟪uEv ε m, dTau ε m (single a a 1) f⟫_ℂ := hU
  rw [hU', inner_uEv, ev_dTau_Eaa hm, inner_smul_left, inner_uEv]
  simp

theorem not_cone_neg_root {a b : Fin n} (hab : a < b) (c : Fin n → Fin n → ℕ) (hc : ∀ a' b', c a' b' ≠ 0 → a' < b')
    (h : Pi.single b (1 : ℝ) - Pi.single a 1 = ∑ a', ∑ b', (c a' b' : ℝ) • root a' b') : False := by
  have key := congrArg (fun v : Fin n → ℝ => ∑ i : Fin n, ((i : ℕ) : ℝ) * v i) h
  have hl : ∑ i : Fin n, ((i : ℕ) : ℝ) * (Pi.single b (1 : ℝ) - Pi.single a 1 : Fin n → ℝ) i = (b : ℕ) - (a : ℕ) := by
    simp [mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
  have hr : ∑ i : Fin n, ((i : ℕ) : ℝ) * (∑ a', ∑ b', (c a' b' : ℝ) • root a' b' : Fin n → ℝ) i =
      ∑ a', ∑ b', (c a' b' : ℝ) * (((a' : ℕ) : ℝ) - (b' : ℕ)) := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, root, Pi.sub_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ => ?_
    simp [Pi.single_apply, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [hl, hr] at key
  have hneg : ∑ a', ∑ b', (c a' b' : ℝ) * (((a' : ℕ) : ℝ) - (b' : ℕ)) ≤ 0 := by
    refine Finset.sum_nonpos fun a' _ => Finset.sum_nonpos fun b' _ => ?_
    by_cases h0 : c a' b' = 0
    · simp [h0]
    · have : ((a' : ℕ) : ℝ) < (b' : ℕ) := by exact_mod_cast hc a' b' h0
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
  have : ((a : ℕ) : ℝ) < (b : ℕ) := by exact_mod_cast hab
  linarith

theorem uEv_hw {ε : Fin n → Bool} {m : Fin n → ℤ} (hm : NonnegDom ε m) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    dTau ε m (single a b 1) (uEv ε m) = 0 := by
  set T := modelKType ε hm
  let u : T.V := uEv ε m
  have hwt0 : ∀ c, T.dτ (single c c 1) u = (((m c : ℤ) : ℝ) : ℂ) • u := fun c => uEv_wt hm c
  change T.dτ (single a b 1) u = 0
  by_contra hv
  have hR := KType.kRel T
  set μ : Fin n → ℝ := fun i => ((m i : ℤ) : ℝ) + ((Pi.single a (1 : ℝ) - Pi.single b (1 : ℝ) : Fin n → ℝ) i) with hμ
  have hab' : a ≠ b := hab.ne
  have hwt : ∀ c, T.dτ (single c c 1) (T.dτ (single a b 1) u) = ((μ c : ℝ) : ℂ) • T.dτ (single a b 1) u := by
    intro c
    have h := congrArg (fun F : Module.End ℂ T.V => F u) (hR c c a b rfl he)
    simp only [kunits, LinearMap.sub_apply, Module.End.mul_apply, ContinuousLinearMap.coe_coe] at h
    rw [hwt0 c, map_smul] at h
    have h' := sub_eq_iff_eq_add.mp h
    refine h'.trans ?_
    by_cases hca : c = a
    · have hcb : c ≠ b := hca ▸ hab'
      rw [if_pos hca, if_neg (Ne.symm hcb)]
      subst hca
      simp only [hμ, Pi.sub_apply, Pi.single_apply, if_true, if_neg hcb, ContinuousLinearMap.coe_coe,
        LinearMap.zero_apply, sub_zero]
      push_cast
      module
    · by_cases hcb : c = b
      · rw [if_neg hca, if_pos hcb.symm]
        subst hcb
        simp only [hμ, Pi.sub_apply, Pi.single_apply, if_true, if_neg hca, ContinuousLinearMap.coe_coe,
          LinearMap.zero_apply, zero_sub]
        push_cast
        module
      · rw [if_neg hca, if_neg (Ne.symm hcb)]
        simp only [hμ, Pi.sub_apply, Pi.single_apply, if_neg hca, if_neg hcb, LinearMap.zero_apply, sub_zero]
        push_cast
        module
  obtain ⟨c, hc, hΛ⟩ := HW.KType.weight_le T hv hwt
  apply not_cone_neg_root hab c (fun a' b' h => (hc a' b' h).1)
  rw [← hΛ]
  funext i
  simp [hμ]

theorem evaluation_longest_weyl_one {ε : Fin n → Bool} {m : Fin n → ℤ} : ev ε m (w0 ε m) = 1 := by
  rw [ev_apply]; exact highest_weight_fn_K_one ε m

theorem uEv_eq {ε : Fin n → Bool} {m : Fin n → ℤ} (hm : NonnegDom ε m) :
    uEv ε m = ((‖w0 ε m‖⁻¹ : ℝ) : ℂ) • wN ε m := by
  have hne : uEv ε m ≠ 0 := by
    intro h
    have := inner_uEv (w0 ε m)
    rw [h, inner_zero_left, evaluation_longest_weyl_one] at this
    exact zero_ne_one this
  obtain ⟨-, c, hc⟩ := HW.KType.hw_unique (modelKType ε hm) hne
    ⟨fun a => by rw [kunits, model_dτ]; exact uEv_wt hm a, fun a b hab he => by
      rw [kunits, model_dτ]; exact uEv_hw hm hab he⟩
  rw [model_w] at hc
  have hc' : uEv ε m = c • wN ε m := hc
  have hcv : starRingEnd ℂ c = ev ε m (wN ε m) := by
    rw [← inner_uEv, hc', inner_smul_left, inner_self_eq_norm_sq_to_K, norm_wN]; simp
  have hev : ev ε m (wN ε m) = ((‖w0 ε m‖⁻¹ : ℝ) : ℂ) := by
    rw [wN, map_smul, evaluation_longest_weyl_one, smul_eq_mul, mul_one]
  have : c = ((‖w0 ε m‖⁻¹ : ℝ) : ℂ) := by
    have h2 := congrArg (starRingEnd ℂ) hcv
    rw [Complex.conj_conj, hev, Complex.conj_ofReal] at h2
    exact h2
  rw [hc', this]

theorem ckModel : CompanionTheory.RgFd.CkModel := by
  intro n ε m hm k
  unfold CompanionTheory.RgFd.cK
  rw [model_op, model_w]
  show ‖⟪wN ε m, tauC ε m k (wN ε m)⟫_ℂ‖ = _
  have hw0 : ‖w0 ε m‖ ≠ 0 := norm_ne_zero_iff.2 (highest_weight_vector_ne_zero ε m)
  have h1 : ⟪wN ε m, tauC ε m k (wN ε m)⟫_ℂ = ((‖w0 ε m‖ : ℝ) : ℂ) * ⟪uEv ε m, tauC ε m k (wN ε m)⟫_ℂ := by
    rw [uEv_eq hm, inner_smul_left, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hw0]
    simp
  rw [h1, inner_uEv, ev_apply, tauC_fn]
  show ‖((‖w0 ε m‖ : ℝ) : ℂ) * (wN ε m).fn (1 * k)‖ = _
  rw [one_mul, wN, MV.fn_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hw0]
  simp [w0]

end CompanionTheory.RgFd.CkM
