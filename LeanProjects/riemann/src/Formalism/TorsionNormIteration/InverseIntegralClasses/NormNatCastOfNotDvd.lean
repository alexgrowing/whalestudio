import Formalism.TorsionNormIteration.Statement

noncomputable section

open PowerSeries

universe u

namespace Formalism.LT.ExpP

open Formalism.G

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma norm_natCast_of_not_dvd {p m : ℕ} (hp : p.Prime) (hp1 : ‖(p : K)‖ < 1) (hm : ¬ p ∣ m) :
    ‖(m : K)‖ = 1 := by
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one K m) ?_
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * p + b * m = 1 := by
    have h := Nat.gcd_eq_gcd_ab p m
    rw [Nat.Coprime.gcd_eq_one hcop] at h
    exact ⟨Nat.gcdA p m, Nat.gcdB p m, by push_cast at h; linarith⟩
  have h1 : (1 : K) = (a : K) * (p : K) + (b : K) * (m : K) := by
    have := congrArg (Int.cast : ℤ → K) hab
    push_cast at this
    exact this.symm
  have hle : (1 : ℝ) ≤ max ‖(a : K) * p‖ ‖(b : K) * m‖ := by
    calc (1 : ℝ) = ‖(1 : K)‖ := norm_one.symm
      _ = ‖(a : K) * p + (b : K) * m‖ := by rw [← h1]
      _ ≤ max ‖(a : K) * p‖ ‖(b : K) * m‖ := IsUltrametricDist.norm_add_le_max _ _
  have ha := IsUltrametricDist.norm_intCast_le_one K a
  have hb := IsUltrametricDist.norm_intCast_le_one K b
  rcases le_max_iff.1 hle with h | h
  · rw [norm_mul] at h
    nlinarith [norm_nonneg (p : K), norm_nonneg (a : K)]
  · rw [norm_mul] at h
    nlinarith [norm_nonneg (m : K), norm_nonneg (b : K)]

lemma norm_natCast_eq {p n : ℕ} (hp : p.Prime) (hp1 : ‖(p : K)‖ < 1) (hn : n ≠ 0) :
    ‖(n : K)‖ = ‖(p : K)‖ ^ padicValNat p n := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  haveI := Fact.mk hp
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  rw [padicValNat.mul (pow_ne_zero _ hp.ne_zero) hm0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hm, add_zero]
  push_cast
  rw [norm_mul, norm_pow, norm_natCast_of_not_dvd hp hp1 hm, mul_one]

theorem expIntegral : Formalism.LT.ExpIntegral.{u} := by
  intro K _ _ _ p hp hp1 c hc n
  haveI := Fact.mk hp
  rw [norm_div, norm_pow, norm_natCast_eq hp hp1 (Nat.factorial_ne_zero n)]
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpos : 0 < ‖(p : K)‖ ^ padicValNat p n.factorial := pow_pos (norm_pos_iff.2 hp0) _
  rw [div_le_one hpos]
  have hv : (p - 1) * padicValNat p n.factorial ≤ n := by
    have := sub_one_mul_padicValNat_factorial (p := p) n
    omega
  have hc1 : ‖c‖ ≤ 1 := by
    by_contra h
    push_neg at h
    have := one_le_pow₀ (n := p - 1) h.le
    linarith
  calc ‖c‖ ^ n ≤ ‖c‖ ^ ((p - 1) * padicValNat p n.factorial) :=
        pow_le_pow_of_le_one (norm_nonneg _) hc1 hv
    _ = (‖c‖ ^ (p - 1)) ^ padicValNat p n.factorial := pow_mul _ _ _
    _ ≤ ‖(p : K)‖ ^ padicValNat p n.factorial := pow_le_pow_left₀ (by positivity) hc _

lemma norm_finsum_le {g : ℕ → K} {C : ℝ} (hC : 0 ≤ C) (hg : ∀ n, ‖g n‖ ≤ C) :
    ‖∑ᶠ n, g n‖ ≤ C := by
  by_cases h : (Function.support g).Finite
  · rw [finsum_eq_sum g h]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC (fun i _ => hg i)
  · rw [finsum_of_infinite_support h, norm_zero]
    exact hC

lemma scalar_bound {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : K)‖ < 1) (c : K) (d m : ℕ) (hmd : m < d)
    (hc : ‖(d : K) * c‖ ≤ 1) :
    ‖c * ((p : K) ^ (d - m) * (d.choose m : K))‖ ≤ ‖(p : K)‖ := by
  haveI := Fact.mk hp
  have hP0 : 0 ≤ ‖(p : K)‖ := norm_nonneg _
  have hP1 : ‖(p : K)‖ ≤ 1 := hp1.le
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, n + 1 - m = j + 1 := ⟨n - m, by omega⟩
  have hsym : (n + 1).choose (j + 1) = (n + 1).choose m := by
    rw [← hj]
    exact Nat.choose_symm (by omega)
  have hN : (n + 1).choose m * (j + 1) = (n + 1) * n.choose j := by
    rw [← hsym, Nat.add_one_mul_choose_eq]
  have hnorm : ‖((n + 1).choose m : K)‖ * ‖((j + 1 : ℕ) : K)‖ ≤ ‖((n + 1 : ℕ) : K)‖ := by
    have h := congrArg (fun x : ℕ => ‖(x : K)‖) hN
    simp only [Nat.cast_mul, norm_mul] at h
    rw [h]
    exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K _)
  have hkn : ‖((j + 1 : ℕ) : K)‖ = ‖(p : K)‖ ^ padicValNat p (j + 1) :=
    norm_natCast_eq hp hp1 (Nat.succ_ne_zero j)
  have hv : padicValNat p (j + 1) < j + 1 := by
    have h1 : p ^ padicValNat p (j + 1) ≤ j + 1 := Nat.le_of_dvd (Nat.succ_pos j) pow_padicValNat_dvd
    have h2 : j + 1 < p ^ (j + 1) := Nat.lt_pow_self hp.one_lt
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).1 (lt_of_le_of_lt h1 h2)
  have hcd : ‖c‖ * ‖((n + 1 : ℕ) : K)‖ ≤ 1 := by
    rw [mul_comm, ← norm_mul]
    exact_mod_cast hc
  rw [hj, norm_mul, norm_mul, norm_pow]
  have key : ‖c‖ * ‖((n + 1).choose m : K)‖ * ‖(p : K)‖ ^ padicValNat p (j + 1) ≤ 1 := by
    calc ‖c‖ * ‖((n + 1).choose m : K)‖ * ‖(p : K)‖ ^ padicValNat p (j + 1)
        = ‖c‖ * (‖((n + 1).choose m : K)‖ * ‖((j + 1 : ℕ) : K)‖) := by rw [hkn]; ring
      _ ≤ ‖c‖ * ‖((n + 1 : ℕ) : K)‖ := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ ≤ 1 := hcd
  have hk' : ‖(p : K)‖ ^ (j + 1) =
      ‖(p : K)‖ ^ padicValNat p (j + 1) * ‖(p : K)‖ ^ (j + 1 - padicValNat p (j + 1)) := by
    rw [← pow_add]
    congr 1
    omega
  calc ‖c‖ * (‖(p : K)‖ ^ (j + 1) * ‖((n + 1).choose m : K)‖)
      = (‖c‖ * ‖((n + 1).choose m : K)‖ * ‖(p : K)‖ ^ padicValNat p (j + 1)) *
          ‖(p : K)‖ ^ (j + 1 - padicValNat p (j + 1)) := by rw [hk']; ring
    _ ≤ 1 * ‖(p : K)‖ ^ (j + 1 - padicValNat p (j + 1)) :=
        mul_le_mul_of_nonneg_right key (pow_nonneg hP0 _)
    _ ≤ ‖(p : K)‖ := by
        rw [one_mul]
        exact pow_le_of_le_one hP0 hP1 (by omega)

lemma norm_coeff_monomial_le (m k : ℕ) (e : Fin 2 →₀ ℕ) :
    ‖MvPowerSeries.coeff e
      ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ m * MvPowerSeries.X 1 ^ k)‖ ≤ 1 := by
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, mul_one,
    MvPowerSeries.coeff_monomial]
  split_ifs <;> simp

lemma term_eq (p c : K) (d m : ℕ) :
    c • ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ m * (p • MvPowerSeries.X 1) ^ (d - m) *
      (d.choose m : MvPowerSeries (Fin 2) K)) =
    (c * (p ^ (d - m) * (d.choose m : K))) •
      ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ m * MvPowerSeries.X 1 ^ (d - m)) := by
  simp only [MvPowerSeries.smul_eq_C_mul, mul_pow, map_mul, map_pow, map_natCast]
  ring

lemma term_bound {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : K)‖ < 1) (z : PowerSeries K)
    (hdz : IntegralPS (PowerSeries.derivative K z)) (d : ℕ) (e : Fin 2 →₀ ℕ) :
    ‖coeff d z • MvPowerSeries.coeff e
      (((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) + (p : K) • MvPowerSeries.X 1) ^ d -
        MvPowerSeries.X 0 ^ d)‖ ≤
        ‖(p : K)‖ := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hc : ‖(d : K) * coeff d z‖ ≤ 1 := by
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
    have h := hdz n
    rw [PowerSeries.coeff_derivative] at h
    push_cast
    rw [mul_comm]
    exact h
  rw [add_pow, Finset.sum_range_succ]
  simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, add_sub_cancel_right, map_sum,
    Finset.smul_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun m hm => ?_
  have hmd : m < d := Finset.mem_range.1 hm
  rw [← map_smul (MvPowerSeries.coeff e), term_eq, map_smul, smul_eq_mul, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (norm_coeff_monomial_le _ _ _)).trans
    (scalar_bound hp hp1 _ d m hmd hc)

theorem quasiLogShift : Formalism.LT.QuasiLogShift.{u} := by
  intro K _ _ p hp hp1 z hz0 hdz e
  have ha : PowerSeries.HasSubst
      (MvPowerSeries.X (0 : Fin 2) + (p : K) • MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have hb : PowerSeries.HasSubst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) :=
    PowerSeries.HasSubst.X 0
  unfold Formalism.G.atX
  rw [map_sub, PowerSeries.coeff_subst ha, PowerSeries.coeff_subst hb,
    ← finsum_sub_distrib (PowerSeries.coeff_subst_finite ha z e) (PowerSeries.coeff_subst_finite hb z e)]
  refine norm_finsum_le (norm_nonneg _) fun d => ?_
  rw [← smul_sub, ← map_sub]
  exact term_bound hp hp1 z hdz d e

theorem Formalism.LT.ExpP.ExpIntegral_valid : Formalism.LT.ExpIntegral.{u} := expIntegral

theorem Formalism.LT.ExpP.QuasiLogShift_valid_direct : Formalism.LT.QuasiLogShift.{u} := quasiLogShift

end Formalism.LT.ExpP

theorem Formalism.LT.exp_integral : Formalism.LT.ExpIntegral.{u} := Formalism.LT.ExpP.expIntegral

theorem Formalism.LT.QuasiLogShift_valid : Formalism.LT.QuasiLogShift.{u} := Formalism.LT.ExpP.quasiLogShift
