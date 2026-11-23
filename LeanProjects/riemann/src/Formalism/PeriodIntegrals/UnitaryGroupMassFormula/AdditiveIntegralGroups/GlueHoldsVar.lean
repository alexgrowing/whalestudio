import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.GuLine

noncomputable section

open Classical

namespace PI.AddIntG.Wk

variable {p : ℕ} [Fact p.Prime]

theorem flog_constantCoeff (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.constantCoeff (flog W wq) = 0 := by
  first
  | simp [PI.AddIntG.flog]
  | (rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; simp [PI.AddIntG.flog])
  | (rw [← PowerSeries.coeff_zero_eq_constantCoeff]; simp [PI.AddIntG.flog])

theorem coeff_one_flog {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    PowerSeries.coeff 1 (flog W wq) = 1 := by
  have h' : wq = 1 + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X * wq +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ * PowerSeries.X ^ 2 * wq +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq ^ 2 +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ * PowerSeries.X ^ 4 * wq ^ 2 +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₆ * PowerSeries.X ^ 6 * wq ^ 3 := h
  have hw : PowerSeries.constantCoeff wq = 1 := by
    rw [h']
    simp
  have h2 : (2 : ℂ_[p]) ≠ 0 := by
    first
    | exact two_ne_zero
    | (intro h2z
       have hinj := (algebraMap ℚ_[p] ℂ_[p]).injective
       have h22 : algebraMap ℚ_[p] ℂ_[p] 2 = algebraMap ℚ_[p] ℂ_[p] 0 := by
         rw [map_ofNat, map_zero]; exact h2z
       exact two_ne_zero (hinj h22))
  have hinv : PowerSeries.constantCoeff (PI.AddIntG.omegaW W wq) = 1 := by
    have hc2 : PowerSeries.constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := map_ofNat _ 2
    simp [PI.AddIntG.omegaW, hw, PowerSeries.constantCoeff_inv, h2, hc2]
    first
    | done
    | exact mul_inv_cancel₀ h2
    | field_simp
  have e : PowerSeries.coeff 1 (PI.AddIntG.flog W wq) = PowerSeries.coeff 0 (PI.AddIntG.omegaW W wq) := by
    simp [PI.AddIntG.flog]
  first
  | (rw [e, PowerSeries.coeff_zero_eq_constantCoeff_apply, hinv])
  | (rw [e]; simpa using hinv)
  | simpa [e] using hinv

private theorem hasSubst_of_constantCoeff_eq_zero_additive_integral_groups {K : Type*} [Field K] {a : PowerSeries K}
    (ha : PowerSeries.constantCoeff a = 0) : PowerSeries.HasSubst a := by
  have ha2 : MvPowerSeries.constantCoeff a = 0 := ha
  first
  | exact PowerSeries.HasSubst.of_constantCoeff_zero ha2
  | exact PowerSeries.HasSubst.of_constantCoeff_zero' ha
  | exact PowerSeries.HasSubst.of_constantCoeff_nilpotent (by rw [ha2]; exact IsNilpotent.zero)

private theorem hasSubst_of_mvConstantCoeff_eq_zero {K : Type*} [Field K] {σ : Type*} {b : MvPowerSeries σ K}
    (hb : MvPowerSeries.constantCoeff b = 0) : PowerSeries.HasSubst b := by
  first
  | exact PowerSeries.HasSubst.of_constantCoeff_zero hb
  | exact PowerSeries.HasSubst.of_constantCoeff_nilpotent (by rw [hb]; exact IsNilpotent.zero)

private theorem subst_subst_eq_subst_subst_of_constantCoeff {K : Type*} [Field K] {σ : Type*} {a : PowerSeries K}
    {b : MvPowerSeries σ K} (ha : PowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) (f : PowerSeries K) :
    PowerSeries.subst b (PowerSeries.subst a f) = PowerSeries.subst (PowerSeries.subst b a) f := by
  have ha' := hasSubst_of_constantCoeff_eq_zero_additive_integral_groups ha
  have hb' := hasSubst_of_mvConstantCoeff_eq_zero hb
  first
  | exact PowerSeries.subst_comp_subst_apply ha' hb' f
  | exact PowerSeries.subst_comp_subst_apply (R := K) ha' hb' f
  | exact congrFun (PowerSeries.subst_comp_subst ha' hb') f
  | simp [PowerSeries.subst_comp_subst_apply ha' hb']

private theorem subst_X_eq_self_of_constantCoeff_eq_zero {K : Type*} [Field K] {σ : Type*} {b : MvPowerSeries σ K}
    (hb : MvPowerSeries.constantCoeff b = 0) :
    PowerSeries.subst b (PowerSeries.X : PowerSeries K) = b := by
  have hb' := hasSubst_of_mvConstantCoeff_eq_zero hb
  first
  | exact PowerSeries.subst_X hb'
  | simp [PowerSeries.subst_X hb']

private theorem coeff_pow_eq_zero_of_X_dvd_of_lt {K : Type*} [Field K] {y : PowerSeries K}
    (hy : PowerSeries.X ∣ y) {m d : ℕ} (h : m < d) : PowerSeries.coeff m (y ^ d) = 0 := by
  have hd : (PowerSeries.X : PowerSeries K) ^ d ∣ y ^ d := pow_dvd_pow_of_dvd hy d
  exact (PowerSeries.X_pow_dvd_iff.1 hd) m h

private theorem powerSeries_coeff_subst_eq_sum_range_coeff_mul {K : Type*} [Field K] {y : PowerSeries K}
    (hy : PowerSeries.constantCoeff y = 0) (l : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.subst y l) =
      ∑ d ∈ Finset.range (n + 1), PowerSeries.coeff d l * PowerSeries.coeff n (y ^ d) := by
  have hs := hasSubst_of_constantCoeff_eq_zero_additive_integral_groups hy
  have hX : PowerSeries.X ∣ y := PowerSeries.X_dvd_iff.2 hy
  have e : PowerSeries.coeff n (PowerSeries.subst y l) =
      ∑ᶠ d, PowerSeries.coeff d l • PowerSeries.coeff n (y ^ d) := by
    first
    | exact PowerSeries.coeff_subst' hs l n
    | exact PowerSeries.coeff_subst hs l (Finsupp.single () n)
    | rw [PowerSeries.coeff_subst' hs]
    | simp only [PowerSeries.coeff_subst' hs]
  have hsupp : Function.support (fun d => PowerSeries.coeff d l • PowerSeries.coeff n (y ^ d)) ⊆
      ↑(Finset.range (n + 1)) := by
    intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra hlt
    exact hd (by rw [coeff_pow_eq_zero_of_X_dvd_of_lt hX (by omega), smul_zero])
  rw [e, finsum_eq_sum_of_support_subset _ hsupp]
  simp only [smul_eq_mul]

private theorem X_pow_add_two_dvd_pow_sub_pow_of_X_pow_dvd_sub {K : Type*} [Field K] {y z : PowerSeries K} {n d : ℕ}
    (hy : PowerSeries.X ∣ y) (hz : PowerSeries.X ∣ z) (hyz : PowerSeries.X ^ (n + 1) ∣ y - z)
    (hd : 2 ≤ d) : PowerSeries.X ^ (n + 2) ∣ y ^ d - z ^ d := by
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨b, rfl⟩ := hz
  have hX : (PowerSeries.X : PowerSeries K) ≠ 0 := PowerSeries.X_ne_zero
  have hab : (PowerSeries.X : PowerSeries K) ^ n ∣ a - b := by
    rw [pow_succ', ← mul_sub] at hyz
    exact (mul_dvd_mul_iff_left hX).1 hyz
  have h1 : a - b ∣ a ^ d - b ^ d := sub_dvd_pow_sub_pow a b d
  have h2 : (PowerSeries.X : PowerSeries K) ^ 2 ∣ PowerSeries.X ^ d := pow_dvd_pow _ hd
  have h3 : (PowerSeries.X : PowerSeries K) ^ (n + 2) =
      PowerSeries.X ^ 2 * PowerSeries.X ^ n := by ring
  rw [h3, mul_pow, mul_pow, ← mul_sub]
  exact mul_dvd_mul h2 (hab.trans h1)

private theorem eq_of_subst_eq_subst_of_coeff_one_eq_one {K : Type*} [Field K] {l y z : PowerSeries K}
    (hl1 : PowerSeries.coeff 1 l = 1) (hy : PowerSeries.constantCoeff y = 0)
    (hz : PowerSeries.constantCoeff z = 0)
    (h : PowerSeries.subst y l = PowerSeries.subst z l) : y = z := by
  have hXy : PowerSeries.X ∣ y := PowerSeries.X_dvd_iff.2 hy
  have hXz : PowerSeries.X ∣ z := PowerSeries.X_dvd_iff.2 hz
  have key : ∀ n : ℕ, (PowerSeries.X : PowerSeries K) ^ (n + 1) ∣ y - z := by
    intro n
    induction n with
    | zero =>
      rw [zero_add, pow_one, PowerSeries.X_dvd_iff, map_sub, hy, hz, sub_zero]
    | succ n ih =>
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      by_cases hm' : m < n + 1
      · exact PowerSeries.X_pow_dvd_iff.1 ih m hm'
      · have hmn : m = n + 1 := by omega
        subst hmn
        have e : PowerSeries.coeff (n + 1) (PowerSeries.subst y l) =
            PowerSeries.coeff (n + 1) (PowerSeries.subst z l) := by rw [h]
        rw [powerSeries_coeff_subst_eq_sum_range_coeff_mul hy, powerSeries_coeff_subst_eq_sum_range_coeff_mul hz] at e
        have h1 : 1 ∈ Finset.range (n + 1 + 1) := by simp
        have sy : ∑ d ∈ Finset.range (n + 1 + 1), PowerSeries.coeff d l * PowerSeries.coeff (n + 1) (y ^ d) =
            PowerSeries.coeff 1 l * PowerSeries.coeff (n + 1) (y ^ 1) +
              ∑ d ∈ (Finset.range (n + 1 + 1)).erase 1,
                PowerSeries.coeff d l * PowerSeries.coeff (n + 1) (y ^ d) :=
          (Finset.add_sum_erase (Finset.range (n + 1 + 1))
            (fun d => PowerSeries.coeff d l * PowerSeries.coeff (n + 1) (y ^ d)) h1).symm
        have sz : ∑ d ∈ Finset.range (n + 1 + 1), PowerSeries.coeff d l * PowerSeries.coeff (n + 1) (z ^ d) =
            PowerSeries.coeff 1 l * PowerSeries.coeff (n + 1) (z ^ 1) +
              ∑ d ∈ (Finset.range (n + 1 + 1)).erase 1,
                PowerSeries.coeff d l * PowerSeries.coeff (n + 1) (z ^ d) :=
          (Finset.add_sum_erase (Finset.range (n + 1 + 1))
            (fun d => PowerSeries.coeff d l * PowerSeries.coeff (n + 1) (z ^ d)) h1).symm
        have hrest : ∑ d ∈ (Finset.range (n + 1 + 1)).erase 1,
              PowerSeries.coeff d l * PowerSeries.coeff (n + 1) (y ^ d) =
            ∑ d ∈ (Finset.range (n + 1 + 1)).erase 1,
              PowerSeries.coeff d l * PowerSeries.coeff (n + 1) (z ^ d) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.mem_erase] at hd
          have hc : PowerSeries.coeff (n + 1) (y ^ d) = PowerSeries.coeff (n + 1) (z ^ d) := by
            rcases Nat.lt_or_ge d 2 with hd2 | hd2
            · have hd0 : d = 0 := by omega
              subst hd0
              simp
            · have hdv := X_pow_add_two_dvd_pow_sub_pow_of_X_pow_dvd_sub hXy hXz ih hd2
              have hzero := PowerSeries.X_pow_dvd_iff.1 hdv (n + 1) (by omega)
              rw [map_sub, sub_eq_zero] at hzero
              exact hzero
          rw [hc]
        rw [sy, sz, hrest, pow_one, pow_one, hl1, one_mul, one_mul] at e
        rw [map_sub, add_right_cancel e, sub_self]
  have hzero : y - z = 0 := by
    ext n
    rw [map_zero]
    exact PowerSeries.X_pow_dvd_iff.1 (key n) n (Nat.lt_succ_self n)
  exact sub_eq_zero.1 hzero

theorem subst_left_inv {K : Type*} [Field K] {l ex : PowerSeries K} (hl0 : PowerSeries.constantCoeff l = 0)
    (hl1 : PowerSeries.coeff 1 l = 1) (hex0 : PowerSeries.constantCoeff ex = 0)
    (h : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.subst l ex = PowerSeries.X := by
  have hy0 : PowerSeries.constantCoeff (PowerSeries.subst l ex) = 0 := by
    first
    | (rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, powerSeries_coeff_subst_eq_sum_range_coeff_mul hl0]; simp [hex0])
    | (have h00 := powerSeries_coeff_subst_eq_sum_range_coeff_mul hl0 ex 0
       simp [hex0] at h00
       simpa using h00)
    | (obtain ⟨e, he⟩ := PowerSeries.X_dvd_iff.2 hex0
       rw [he, PowerSeries.subst_mul (hasSubst_of_constantCoeff_eq_zero_additive_integral_groups hl0), subst_X_eq_self_of_constantCoeff_eq_zero hl0, map_mul, hl0, zero_mul])
  have hXl : PowerSeries.subst (PowerSeries.X : PowerSeries K) l = l := by
    first
    | exact PowerSeries.subst_self l
    | (ext n
       rw [powerSeries_coeff_subst_eq_sum_range_coeff_mul PowerSeries.constantCoeff_X]
       simp [PowerSeries.coeff_X_pow])
  have heq : PowerSeries.subst (PowerSeries.subst l ex) l = PowerSeries.subst PowerSeries.X l := by
    rw [← subst_subst_eq_subst_subst_of_constantCoeff hex0 hl0 l, h, subst_X_eq_self_of_constantCoeff_eq_zero hl0, hXl]
  exact eq_of_subst_eq_subst_of_coeff_one_eq_one hl1 hy0 PowerSeries.constantCoeff_X heq

theorem add_eq_of {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]} (h : IsWq W wq)
    (hex0 : PowerSeries.constantCoeff ex = 0) (hex : PowerSeries.subst ex (flog W wq) = PowerSeries.X)
    (F : MvPowerSeries (Fin 2) ℂ_[p]) (hF0 : MvPowerSeries.constantCoeff F = 0)
    (hF : PowerSeries.subst F (flog W wq) =
      PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (flog W wq) +
        PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) (flog W wq)) :
    add (flog W wq) ex (Xv 0) (Xv 1) = F := by
  have hl0 := flog_constantCoeff W wq
  have hl1 := coeff_one_flog h
  have hinv := subst_left_inv hl0 hl1 hex0 hex
  first
  | unfold PI.AddIntG.add
  | simp only [PI.AddIntG.add]
  rw [← hF, ← subst_subst_eq_subst_subst_of_constantCoeff hl0 hF0 ex, hinv, subst_X_eq_self_of_constantCoeff_eq_zero hF0]

theorem exists_intS (p : ℕ) [Fact p.Prime] : ∃ S : Subring ℂ_[p], ∀ x, x ∈ S ↔ ‖x‖ ≤ 1 := by
  have hadd : ∀ a b : ℂ_[p], ‖a + b‖ ≤ max ‖a‖ ‖b‖ := by
    first
    | exact fun a b => IsUltrametricDist.norm_add_le_max a b
    | exact fun a b => (IsUltrametricDist.isNonarchimedean_norm (R := ℂ_[p])) a b
  refine ⟨{ carrier := {x | ‖x‖ ≤ 1},
            mul_mem' := fun {a b} ha hb => ?_,
            one_mem' := ?_,
            add_mem' := fun {a b} ha hb => ?_,
            zero_mem' := ?_,
            neg_mem' := fun {a} ha => ?_ }, fun x => by first | exact Iff.rfl | simp⟩
  · change ‖a‖ ≤ 1 at ha
    change ‖b‖ ≤ 1 at hb
    change ‖a * b‖ ≤ 1
    rw [norm_mul]
    nlinarith [norm_nonneg a, norm_nonneg b]
  · change ‖(1 : ℂ_[p])‖ ≤ 1
    simp
  · change ‖a‖ ≤ 1 at ha
    change ‖b‖ ≤ 1 at hb
    change ‖a + b‖ ≤ 1
    exact (hadd a b).trans (max_le ha hb)
  · change ‖(0 : ℂ_[p])‖ ≤ 1
    simp
  · change ‖a‖ ≤ 1 at ha
    change ‖-a‖ ≤ 1
    rwa [norm_neg]

theorem glue_holds_var : Glue := by
  unfold PI.AddIntG.Glue PI.AddIntG.Target
  intro hlaw p _ W wq ex ha1 ha2 ha3 ha4 ha6 hW hex0 hex
  unfold PI.AddIntG.KeyF at hlaw
  obtain ⟨S, hS⟩ := exists_intS p
  refine ⟨?_, ?_⟩
  · obtain ⟨F, hFS, hF0, hF⟩ := hlaw p S W wq ((hS _).2 ha1) ((hS _).2 ha2) ((hS _).2 ha3)
      ((hS _).2 ha4) ((hS _).2 ha6) hW
    rw [add_eq_of hW hex0 hex F hF0 hF]
    intro n
    exact (hS _).1 (hFS n)
  · rintro ⟨h1, h2, h3, h4, h6⟩
    obtain ⟨F, hFS, hF0, hF⟩ := hlaw p (PI.AddIntG.Wp p) W wq h1 h2 h3 h4 h6 hW
    rw [add_eq_of hW hex0 hex F hF0 hF]
    exact hFS

end PI.AddIntG.Wk
