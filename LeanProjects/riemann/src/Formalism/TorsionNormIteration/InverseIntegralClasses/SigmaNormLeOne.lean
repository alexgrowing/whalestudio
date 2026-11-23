import Formalism.TorsionNormIteration.InvIntegralOfClass

noncomputable section

open PowerSeries

universe u v

namespace Formalism.LT.CoeffP

open Formalism.G

section Ball

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma sigma_norm_le_one {p q : ℕ} {σ : K →+* K} (hp : ‖(p : K)‖ ≤ 1)
    (hσ : IsFrobLift p q σ) (a : K) (ha : ‖a‖ ≤ 1) : ‖σ a‖ ≤ 1 := by
  have h1 : ‖σ a - a ^ q‖ ≤ ‖(p : K)‖ := hσ a ha
  have h2 : ‖a ^ q‖ ≤ 1 := by
    rw [norm_pow]
    simpa using pow_le_pow_of_le_one (norm_nonneg a) ha (Nat.zero_le q)
  calc ‖σ a‖ = ‖(σ a - a ^ q) + a ^ q‖ := by rw [sub_add_cancel]
    _ ≤ max ‖σ a - a ^ q‖ ‖a ^ q‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le (h1.trans hp) h2

lemma coeff_split (p q : ℕ) (hq : q ≠ 0) (σ : K →+* K) (f : PowerSeries K) (n : ℕ) :
    coeff n f = coeff n (f - (p : K)⁻¹ • (PowerSeries.map σ f).subst
        ((PowerSeries.X : PowerSeries K) ^ q)) +
      (p : K)⁻¹ * (if q ∣ n then σ (coeff (n / q) f) else 0) := by
  rw [map_sub, map_smul, PowerSeries.coeff_subst_X_pow hq, PowerSeries.coeff_map, smul_eq_mul]
  split_ifs <;> simp

end Ball

private lemma norm_add_inv_mul_mul_norm_pow_succ_le_one {L : Type*} [NormedField L] [IsUltrametricDist L] (a s π : L) (k : ℕ)
    (ha : ‖a‖ ≤ 1) (hs : ‖s‖ * ‖π‖ ^ k ≤ 1) (hπ : ‖π‖ ≤ 1) (hπ0 : π ≠ 0) :
    ‖a + π⁻¹ * s‖ * ‖π‖ ^ (k + 1) ≤ 1 := by
  have hn : 0 < ‖π‖ := norm_pos_iff.mpr hπ0
  have hpow0 : 0 ≤ ‖π‖ ^ (k + 1) := pow_nonneg hn.le _
  have hpow1 : ‖π‖ ^ (k + 1) ≤ 1 := by
    simpa using pow_le_pow_of_le_one hn.le hπ (Nat.zero_le (k + 1))
  refine (mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) hpow0).trans ?_
  rw [max_mul_of_nonneg _ _ hpow0]
  refine max_le ?_ ?_
  · calc ‖a‖ * ‖π‖ ^ (k + 1) ≤ 1 * 1 := mul_le_mul ha hpow1 hpow0 zero_le_one
      _ = 1 := one_mul 1
  · calc ‖π⁻¹ * s‖ * ‖π‖ ^ (k + 1) = ‖s‖ * ‖π‖ ^ k * (‖π‖⁻¹ * ‖π‖) := by
          rw [norm_mul, norm_inv, pow_succ]; ring
      _ = ‖s‖ * ‖π‖ ^ k := by rw [inv_mul_cancel₀ hn.ne', mul_one]
      _ ≤ 1 := hs

theorem coeffBound : Formalism.LT.CoeffBound.{u} := by
  unfold Formalism.LT.CoeffBound
  intro K _ _ _ p q σ hset f hf0 hfe n
  have hset' : Nat.Prime p ∧ (∃ e, 0 < e ∧ q = p ^ e) ∧ ‖(p : K)‖ < 1 ∧ Formalism.G.IsFrobLift p q σ :=
    hset
  obtain ⟨hp, ⟨e, he, hqe⟩, hp1, hσ⟩ := hset'
  have hq2 : 2 ≤ q := by
    rw [hqe]
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos (Nat.succ_le_of_lt he)
  have hq0 : q ≠ 0 := by omega
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero

  have hσb : ∀ (x : K) (k : ℕ), ‖x‖ * ‖(p : K)‖ ^ k ≤ 1 → ‖σ x‖ * ‖(p : K)‖ ^ k ≤ 1 := by
    intro x k hx
    have h1 : ‖x * (p : K) ^ k‖ ≤ 1 := by rw [norm_mul, norm_pow]; exact hx
    have h2 := sigma_norm_le_one hp1.le hσ _ h1
    rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow] at h2
    exact h2
  refine Nat.strong_induction_on n ?_
  intro n ih
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨0, dvd_zero _, ?_⟩
    have h0 : PowerSeries.coeff 0 f = 0 := by simpa using hf0
    rw [h0, norm_zero, zero_mul]
    exact zero_le_one
  · have hg : ‖PowerSeries.coeff n (f - (p : K)⁻¹ •
        (PowerSeries.map σ f).subst ((PowerSeries.X : PowerSeries K) ^ q))‖ ≤ 1 := hfe n
    rw [coeff_split p q hq0 σ f n]
    by_cases hdiv : q ∣ n
    · have hlt : n / q < n := Nat.div_lt_self hn (by omega)
      obtain ⟨k, hk, hkb⟩ := ih (n / q) hlt
      refine ⟨k + 1, ?_, ?_⟩
      · have hnq : n = q * (n / q) := (Nat.mul_div_cancel' hdiv).symm
        rw [hnq, pow_succ']
        exact mul_dvd_mul_left q hk
      · rw [if_pos hdiv]
        exact norm_add_inv_mul_mul_norm_pow_succ_le_one _ _ _ k hg (hσb _ _ hkb) hp1.le hpK
    · refine ⟨0, by rw [pow_zero]; exact one_dvd n, ?_⟩
      rw [if_neg hdiv, mul_zero, add_zero, pow_zero, mul_one]
      exact hg

section Bd

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v}

def Bd (c : ℝ) (F : MvPowerSeries ι K) : Prop := ∀ d : ι →₀ ℕ, ‖MvPowerSeries.coeff d F‖ ≤ c

lemma Bd.mono {a b : ℝ} {F : MvPowerSeries ι K} (hF : Bd a F) (h : a ≤ b) : Bd b F := by
  intro d
  exact (hF d).trans h

lemma Bd.mul {a b : ℝ} {F G : MvPowerSeries ι K} (hF : Bd a F) (hG : Bd b G) (ha : 0 ≤ a)
    (hb : 0 ≤ b) : Bd (a * b) (F * G) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) (fun x _ => ?_)
  rw [norm_mul]
  exact mul_le_mul (hF x.1) (hG x.2) (norm_nonneg _) ha

lemma Bd.one : Bd 1 (1 : MvPowerSeries ι K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp

lemma Bd.pow {a : ℝ} {F : MvPowerSeries ι K} (hF : Bd a F) (ha : 0 ≤ a) :
    ∀ n : ℕ, Bd (a ^ n) (F ^ n)
  | 0 => by simpa using (Bd.one : Bd 1 (1 : MvPowerSeries ι K))
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact (Bd.pow hF ha n).mul hF (pow_nonneg ha n) ha

lemma Bd.sum {α : Type*} {a : ℝ} (ha : 0 ≤ a) {s : Finset α} {F : α → MvPowerSeries ι K}
    (h : ∀ i ∈ s, Bd a (F i)) : Bd a (∑ i ∈ s, F i) := by
  intro d
  rw [map_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg ha (fun i hi => h i hi d)

lemma Bd.mul_natCast {a : ℝ} {F : MvPowerSeries ι K} (hF : Bd a F) (n : ℕ) :
    Bd (‖(n : K)‖ * a) (F * (n : MvPowerSeries ι K)) := by
  intro d
  rw [mul_comm F, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hF d) (norm_nonneg _)

private lemma bd_add' {c : ℝ} {F G : MvPowerSeries ι K} (hF : Bd c F) (hG : Bd c G) :
    Bd c (F + G) := by
  intro d
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hF d) (hG d))

lemma powp_step {p : ℕ} (hp : p.Prime) {r : ℕ} (hr : 1 ≤ r) {A B : MvPowerSeries ι K}
    (_hA : Bd 1 A) (hB : Bd 1 B) (hD : Bd (‖(p : K)‖ ^ r) (A - B)) :
    Bd (‖(p : K)‖ ^ (r + 1)) (A ^ p - B ^ p) := by
  have hpn : 0 ≤ ‖(p : K)‖ := norm_nonneg _
  have hp1 : ‖(p : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K p

  have hexp : A ^ p - B ^ p = ∑ m ∈ Finset.range p,
      (A - B) ^ (m + 1) * B ^ (p - (m + 1)) * ((p.choose (m + 1) : ℕ) : MvPowerSeries ι K) := by
    have h := add_pow (A - B) B p
    rw [sub_add_cancel, Finset.sum_range_succ'] at h
    rw [h, pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
      add_sub_cancel_right]
  rw [hexp]
  refine Bd.sum (pow_nonneg hpn _) (fun m hm => ?_)
  have hm' : m < p := Finset.mem_range.mp hm
  have hDm : Bd (‖(p : K)‖ ^ (r * (m + 1))) ((A - B) ^ (m + 1)) := by
    rw [pow_mul]
    exact Bd.pow hD (pow_nonneg hpn _) (m + 1)
  have hBm : Bd 1 (B ^ (p - (m + 1))) := by
    have h := Bd.pow hB zero_le_one (p - (m + 1))
    rwa [one_pow] at h
  have hprod : Bd (‖(p : K)‖ ^ (r * (m + 1))) ((A - B) ^ (m + 1) * B ^ (p - (m + 1))) := by
    have h := Bd.mul hDm hBm (pow_nonneg hpn _) zero_le_one
    rwa [mul_one] at h
  refine Bd.mono (Bd.mul_natCast hprod (p.choose (m + 1))) ?_
  rcases Nat.lt_or_ge (m + 1) p with hlt | hge
  ·
    obtain ⟨t, ht⟩ := hp.dvd_choose_self (Nat.succ_ne_zero m) hlt
    have hc : ‖((p.choose (m + 1) : ℕ) : K)‖ ≤ ‖(p : K)‖ := by
      rw [ht, Nat.cast_mul, norm_mul]
      calc ‖(p : K)‖ * ‖(t : K)‖ ≤ ‖(p : K)‖ * 1 :=
            mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_natCast_le_one K t) hpn
        _ = ‖(p : K)‖ := mul_one _
    have hr' : ‖(p : K)‖ ^ (r * (m + 1)) ≤ ‖(p : K)‖ ^ r :=
      pow_le_pow_of_le_one hpn hp1 (Nat.le_mul_of_pos_right r (Nat.succ_pos m))
    calc ‖((p.choose (m + 1) : ℕ) : K)‖ * ‖(p : K)‖ ^ (r * (m + 1))
        ≤ ‖(p : K)‖ * ‖(p : K)‖ ^ r := mul_le_mul hc hr' (pow_nonneg hpn _) hpn
      _ = ‖(p : K)‖ ^ (r + 1) := by ring
  ·
    have hm1 : m + 1 = p := Nat.le_antisymm (Nat.succ_le_of_lt hm') hge
    rw [hm1, Nat.choose_self, Nat.cast_one, norm_one, one_mul]
    apply pow_le_pow_of_le_one hpn hp1
    calc r + 1 ≤ r * 2 := by omega
      _ ≤ r * p := Nat.mul_le_mul_left r hp.two_le

lemma powpj {p : ℕ} (hp : p.Prime) {r : ℕ} (hr : 1 ≤ r) {A B : MvPowerSeries ι K}
    (hA : Bd 1 A) (hB : Bd 1 B) (hD : Bd (‖(p : K)‖ ^ r) (A - B)) :
    ∀ j : ℕ, Bd (‖(p : K)‖ ^ (r + j)) (A ^ (p ^ j) - B ^ (p ^ j))
  | 0 => by simpa using hD
  | j + 1 => by
    rw [pow_succ p j, pow_mul, pow_mul, ← add_assoc]
    exact powp_step hp (by omega) (by simpa using hA.pow zero_le_one (p ^ j))
      (by simpa using hB.pow zero_le_one (p ^ j)) (powpj hp hr hA hB hD j)

lemma pow_sub_pow_bd {c : ℝ} (hc : 0 ≤ c) {A B : MvPowerSeries ι K} (hA : Bd 1 A) (hB : Bd 1 B)
    (hD : Bd c (A - B)) (m : ℕ) : Bd c (A ^ m - B ^ m) := by
  induction m with
  | zero =>
    intro d
    simp [hc]
  | succ m ih =>
    have hAm : Bd 1 (A ^ m) := by simpa using Bd.pow hA zero_le_one m
    have e : A ^ (m + 1) - B ^ (m + 1) = A ^ m * (A - B) + (A ^ m - B ^ m) * B := by ring
    rw [e]
    have h1 : Bd c (A ^ m * (A - B)) := by simpa using Bd.mul hAm hD zero_le_one hc
    have h2 : Bd c ((A ^ m - B ^ m) * B) := by simpa using Bd.mul ih hB hc zero_le_one
    exact bd_add' h1 h2

end Bd

theorem powCongr : Formalism.LT.PowCongr.{u, v} := by
  unfold Formalism.LT.PowCongr
  intro K _ _ ι p hp A B hA hB r hr hD j m
  have hA' : Bd 1 A := hA
  have hB' : Bd 1 B := hB
  have hD' : Bd (‖(p : K)‖ ^ r) (A - B) := by
    intro d
    rw [← norm_pow]
    exact hD d
  have h1 := powpj hp hr hA' hB' hD' j
  have hAj : Bd 1 (A ^ (p ^ j)) := by simpa using Bd.pow hA' zero_le_one (p ^ j)
  have hBj : Bd 1 (B ^ (p ^ j)) := by simpa using Bd.pow hB' zero_le_one (p ^ j)
  have h2 := pow_sub_pow_bd (pow_nonneg (norm_nonneg _) _) hAj hBj h1 m
  intro d
  rw [norm_pow, pow_mul, pow_mul]
  exact h2 d

end Formalism.LT.CoeffP

theorem Formalism.LT.CoeffBound_valid : Formalism.LT.CoeffBound.{u} := Formalism.LT.CoeffP.coeffBound

theorem Formalism.LT.PowCongr_valid : Formalism.LT.PowCongr.{u, v} := Formalism.LT.CoeffP.powCongr
