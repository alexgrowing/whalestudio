import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.TsumNormEisensteinTranslate
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Lipschitz

open Complex UpperHalfPlane UpperTheory.V.Af

namespace UpperTheory.V.Sd

private lemma lambert (k : ℕ) (hk : 2 ≤ k) {x q : ℂ} (hx : ‖x‖ = 1) (hq : ‖q‖ < 1) :
    ∃ S : ℂ, HasSum (fun m : ℕ => Lk k (x * q ^ (m + 1))) S ∧
      HasSum (fun n : ℕ => (∑ e ∈ (n + 1).divisors, (e : ℂ) ^ (k - 1) * x ^ e) * q ^ (n + 1)) S := by
  have hs : Summable fun c : ℕ+ × ℕ+ => (c.2 : ℂ) ^ (k - 1) * x ^ (c.2 : ℕ) * q ^ (c.1 * c.2 : ℕ) := by
    refine Summable.of_norm_bounded (summable_prod_mul_pow (k - 1) hq).norm fun c => ?_
    simp [norm_pow, hx]
  refine ⟨∑' c : ℕ+ × ℕ+, (c.2 : ℂ) ^ (k - 1) * x ^ (c.2 : ℕ) * q ^ (c.1 * c.2 : ℕ), ?_, ?_⟩
  · rw [← hasSum_pnat_iff_hasSum_succ (f := fun m => Lk k (x * q ^ m))]
    refine hs.hasSum.prod_fiberwise fun m => ?_
    have h1 : ‖x * q ^ (m : ℕ)‖ < 1 := by
      rw [norm_mul, hx, one_mul, norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hq m.ne_zero
    have h2 := (lipschitz k hk).1 _ h1
    rw [← hasSum_nat_add_iff' 1] at h2
    have hk' : k - 1 ≠ 0 := by omega
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_pow hk', zero_mul, sub_zero] at h2
    rw [← hasSum_pnat_iff_hasSum_succ (f := fun e : ℕ => (e : ℂ) ^ (k - 1) * (x * q ^ (m : ℕ)) ^ e)] at h2
    simpa only [mul_pow, pow_mul, mul_assoc] using h2
  · rw [← hasSum_pnat_iff_hasSum_succ (f := fun n => (∑ e ∈ n.divisors, (e : ℂ) ^ (k - 1) * x ^ e) * q ^ n)]
    have h2 := sigmaAntidiagonalEquivProd.hasSum_iff.2 hs.hasSum
    refine h2.sigma fun n => ?_
    refine (congrArg (HasSum _) ?_).mpr (hasSum_fintype _)
    simp only [Function.comp, sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors,
      PNat.mk_coe, Equiv.coe_fn_mk, Finset.univ_eq_attach]
    rw [(n : ℕ).divisorsAntidiagonal.sum_attach
      (fun y : ℕ × ℕ => (y.2 : ℂ) ^ (k - 1) * x ^ y.2 * q ^ (y.1 * y.2)),
      Nat.sum_divisorsAntidiagonal' (fun u y => (y : ℂ) ^ (k - 1) * x ^ y * q ^ (u * y)), Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hi)]

private lemma row (N k : ℕ) [NeZero N] (hk : 2 ≤ k) (b : ℤ) (hb : (b : ZMod N) ≠ 0) (z : ℍ) (m : ℕ) :
    HasSum (fun j : ℤ => (N : ℂ) ^ k / lipC k * ((((N * m : ℤ)) : ℂ) * (z : ℂ) + ((b + N * j : ℤ) : ℂ)) ^ (-(k : ℤ)))
      (Lk k ((ZMod.stdAddChar (b : ZMod N) : ℂ) * (Function.Periodic.qParam 1 z) ^ m)) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hC : lipC k ≠ 0 := by
    unfold lipC
    have := Nat.factorial_ne_zero (k - 1)
    simp [Real.pi_ne_zero, this]
  have h0 : ((b : ℂ) / N).im = 0 := by
    rw [show (b : ℂ) / N = (((b : ℝ) / N : ℝ) : ℂ) by push_cast; rfl, ofReal_im]
  have h := (lipschitz k hk).2 (m * (z : ℂ) + b / N) ?_ ?_
  · have e : cexp (2 * Real.pi * Complex.I * (m * (z : ℂ) + b / N)) =
        (ZMod.stdAddChar (b : ZMod N) : ℂ) * (Function.Periodic.qParam 1 z) ^ m := by
      rw [ZMod.stdAddChar_coe, Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [e] at h
    have h' := h.mul_left (lipC k)⁻¹
    rw [inv_mul_cancel_left₀ hC] at h'
    refine (congrArg (fun F => HasSum F _) (funext fun j => ?_)).mpr (h')
    have : (((N * m : ℤ)) : ℂ) * (z : ℂ) + ((b + N * j : ℤ) : ℂ) = N * (m * (z : ℂ) + b / N + j) := by
      push_cast
      field_simp
      ring
    rw [this, mul_zpow, zpow_neg (N : ℂ), zpow_natCast]
    field_simp
  · have := z.im_pos
    simp [h0]
    positivity
  · intro j hj
    have h1 := congrArg Complex.im hj
    have := z.im_pos.ne'
    simp [h0, this] at h1
    subst h1
    apply hb
    have : (b : ℂ) = ((N * j : ℤ) : ℂ) := by
      push_cast
      rw [← hj]
      field_simp
      simp
    rw [Int.cast_injective this]
    simp

private lemma reindex (N k : ℕ) [NeZero N] (hk : 3 ≤ k) (b : ℤ) (z : ℍ) :
    HasSum (fun c : ℤ × ℤ => (N : ℂ) ^ k / lipC k *
      ((((N * c.1 : ℤ)) : ℂ) * (z : ℂ) + ((b + N * c.2 : ℤ) : ℂ)) ^ (-(k : ℤ))) (eisFun N k (b : ZMod N) z) := by
  have hN : (N : ℤ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hs : Summable fun v : ℤ × ℤ => ((v.1 : ℂ) * (z : ℂ) + (v.2 : ℂ)) ^ (-(k : ℤ)) := by
    have := (EisensteinSeries.summable_norm_eisSummand (k := k) (by exact_mod_cast hk) z).of_norm
    rw [← (finTwoArrowEquiv ℤ).symm.summable_iff] at this
    exact this
  let g : ℤ × ℤ → {v : ℤ × ℤ // (v.1 : ZMod N) = 0 ∧ (v.2 : ZMod N) = (b : ZMod N)} :=
    fun c => ⟨(N * c.1, b + N * c.2), by simp⟩
  have hg : Function.Bijective g := by
    constructor
    · rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
      simpa [g, hN, NeZero.ne N] using h
    · rintro ⟨⟨v1, v2⟩, h1, h2⟩
      obtain ⟨c1, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h1
      obtain ⟨c2, h⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h2.symm
      refine ⟨(c1, c2), Subtype.ext (Prod.ext rfl ?_)⟩
      simp only [g] at h ⊢
      omega
  have h := ((Equiv.ofBijective g hg).hasSum_iff.2 (hs.subtype _).hasSum).mul_left ((N : ℂ) ^ k / lipC k)
  exact h

private lemma expansion (N k : ℕ) [NeZero N] (hk : 3 ≤ k) (b : ℤ) (hb : (b : ZMod N) ≠ 0) (z : ℍ) :
    HasSum (fun n : ℕ => (if n = 0 then Lk k (ZMod.stdAddChar (b : ZMod N) : ℂ) else
      ∑ e ∈ n.divisors, (e : ℂ) ^ (k - 1) * ((ZMod.stdAddChar ((b : ZMod N) * (e : ZMod N)) : ℂ) +
        (-1) ^ k * (ZMod.stdAddChar (-((b : ZMod N) * (e : ZMod N))) : ℂ))) • (Function.Periodic.qParam 1 z) ^ n)
      (eisFun N k (b : ZMod N) z) := by
  set q := Function.Periodic.qParam 1 (z : ℂ) with hqd
  have hq : ‖q‖ < 1 := by simpa using UpperHalfPlane.norm_qParam_lt_one 1 z
  have hk2 : 2 ≤ k := by omega
  have hn : ∀ c : ZMod N, ‖(ZMod.stdAddChar c : ℂ)‖ = 1 := fun c => by
    rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _
  obtain ⟨S, hS1, hS2⟩ := lambert k hk2 (hn b) hq
  obtain ⟨T, hT1, hT2⟩ := lambert k hk2 (hn (-b)) hq
  let g : ℤ → ℂ := fun m => if 0 ≤ m then Lk k ((ZMod.stdAddChar (b : ZMod N) : ℂ) * q ^ m.toNat) else
    (-1) ^ k * Lk k ((ZMod.stdAddChar (-(b : ZMod N)) : ℂ) * q ^ (-m).toNat)
  have h1 : HasSum g (eisFun N k (b : ZMod N) z) := by
    refine (reindex N k hk b z).prod_fiberwise fun m => ?_
    by_cases hm : 0 ≤ m
    · lift m to ℕ using hm
      simpa only [g, Nat.cast_nonneg, if_true, Int.toNat_natCast] using row N k hk2 b hb z m
    · obtain ⟨m, rfl⟩ : ∃ m' : ℕ, m = -(m' : ℤ) := ⟨(-m).toNat, by omega⟩
      have h := (row N k hk2 (-b) (by simpa using hb) z m).mul_left ((-1) ^ k)
      rw [← (Equiv.neg ℤ).hasSum_iff] at h
      simp only [g, if_neg hm, neg_neg, Int.toNat_natCast]
      rw [Int.cast_neg] at h
      refine (congrArg (fun F => HasSum F _) (funext fun j => ?_)).mpr (h)
      have : (((N * -(m : ℤ) : ℤ)) : ℂ) * (z : ℂ) + ((b + N * j : ℤ) : ℂ) =
          (-1) * ((((N * m : ℤ)) : ℂ) * (z : ℂ) + ((-b + N * -j : ℤ) : ℂ)) := by
        push_cast
        ring
      simp only [Function.comp, Equiv.neg_apply]
      rw [this, mul_zpow, zpow_neg (-1 : ℂ), zpow_natCast, ← inv_pow, inv_neg_one]
      ring
  have h2 : HasSum g ((Lk k (ZMod.stdAddChar (b : ZMod N) : ℂ) + S) + (-1) ^ k * T) := by
    refine HasSum.of_nat_of_neg_add_one ?_ ?_
    · have := HasSum.zero_add (f := fun m : ℕ => Lk k ((ZMod.stdAddChar (b : ZMod N) : ℂ) * q ^ m)) hS1
      simpa [g] using this
    · refine (congrArg (fun F => HasSum F _) (funext fun n => ?_)).mpr (hT1.mul_left ((-1) ^ k))
      have : ¬ (0 : ℤ) ≤ -((n : ℤ) + 1) := by omega
      simp only [g, if_neg this, neg_neg]
      rfl
  rw [h1.unique h2, add_assoc, ← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, if_true, pow_zero, smul_eq_mul, mul_one, add_sub_cancel_left,
    Nat.succ_ne_zero, if_false]
  refine (congrArg (fun F => HasSum F _) (funext fun n => ?_)).mpr (hS2.add (hT2.mul_left ((-1) ^ k)))
  rw [← mul_assoc, ← add_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← AddChar.map_nsmul_eq_pow, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, nsmul_eq_mul, mul_neg, mul_comm (e : ZMod N)]
  ring

end UpperTheory.V.Sd

theorem UpperTheory.V.Sd.eisCoef :
    UpperTheory.V.Sd.EisCoef := by
  intro N k _ hk a ha
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective a
  obtain ⟨f, hf⟩ := UpperTheory.V.Sd.eisMF N k hk b
  have h := ModularFormClass.qExpansion_coeff_unique (f := f) one_pos
    (by rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples 1)
    (fun τ => by rw [hf]; exact UpperTheory.V.Sd.expansion N k hk b ha τ)
  rw [hf] at h
  refine ⟨(h 0).symm, fun n hn => ?_⟩
  rw [UpperTheory.V.Af.coef, ← h n, if_neg (by omega)]
