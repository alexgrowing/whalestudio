import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.FrobeniusCongruenceWitt

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF altF)
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence (altR)

variable (p : ℕ) [hp : Fact p.Prime] (K' : Type) [Field K'] [Algebra (K0 p) K']

theorem sx_lam_int (vp : K') (hvp : vp ^ (p ^ 2 - 1) = (p : K')) (n : ℕ) :
    ∃ z : ℤ, PowerSeries.coeff n (lamF p vp) = (z : K') ∧
      (p : ℤ) ∣ z - ((if n = 1 then 1 else 0) + (if n = p ^ 2 then 1 else 0)) := by
  haveI := charZero_K' p K'
  have hp2 : 2 ≤ p := hp.out.two_le
  have hq : 4 ≤ p ^ 2 := by nlinarith
  have hinj : Function.Injective (fun j : ℕ => (p ^ 2) ^ j) := Nat.pow_right_injective (by omega)
  have hp0 : (p : K') ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hq1 : p ^ 2 ≠ 1 := by omega
  simp only [lamF, lgF, PowerSeries.coeff_mk]
  by_cases hn : ∃ j, n = (p ^ 2) ^ j
  · obtain ⟨j, rfl⟩ := hn
    have hjlt : j < (p ^ 2) ^ j + 1 := by
      have := Nat.lt_pow_self (n := j) (show 1 < p ^ 2 by omega)
      omega
    have hsum : (∑ i ∈ range ((p ^ 2) ^ j + 1),
        if (p ^ 2) ^ j = (p ^ 2) ^ i then ((p : K') ^ i)⁻¹ else 0) = ((p : K') ^ j)⁻¹ := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        rw [if_neg]
        intro h
        exact hb (hinj h).symm
      · intro hj
        exact absurd (Finset.mem_range.2 hjlt) hj
    rw [hsum]
    have key : ∀ m : ℕ, ∃ e : ℕ, vp ^ ((p ^ 2) ^ m - 1) = (p : K') ^ e ∧ m ≤ e ∧
        (m ≤ 1 → e = m) ∧ (2 ≤ m → m + 1 ≤ e) := by
      intro m
      induction m with
      | zero => exact ⟨0, by simp, le_rfl, fun _ => rfl, fun h => by omega⟩
      | succ m ih =>
        obtain ⟨e, he, hme, h1, h2⟩ := ih
        have ha : 1 ≤ (p ^ 2) ^ m := Nat.one_le_pow _ _ (by omega)
        have hexp : (p ^ 2) ^ (m + 1) - 1 = ((p ^ 2) ^ m - 1) * p ^ 2 + (p ^ 2 - 1) := by
          rw [pow_succ]
          have : 1 ≤ (p ^ 2) ^ m * p ^ 2 := Nat.one_le_iff_ne_zero.2 (by positivity)
          zify [ha, this, show 1 ≤ p ^ 2 by omega]
          ring
        have hm4 : e * 4 ≤ e * p ^ 2 := Nat.mul_le_mul_left _ hq
        refine ⟨e * p ^ 2 + 1, ?_, ?_, ?_, ?_⟩
        · rw [hexp, pow_add, pow_mul, he, hvp, ← pow_mul, ← pow_succ]
        · omega
        · intro hm
          have hm0 : m = 0 := by omega
          subst hm0
          have he0 := h1 (by omega)
          subst he0
          simp
        · intro hm
          omega
    obtain ⟨e, he, hje, h1, h2⟩ := key j
    refine ⟨(p : ℤ) ^ (e - j), ?_, ?_⟩
    · rw [he]
      push_cast
      have hpe : (p : K') ^ e = (p : K') ^ (e - j) * (p : K') ^ j := by
        rw [← pow_add, Nat.sub_add_cancel hje]
      rw [hpe, mul_inv_cancel_right₀ (pow_ne_zero _ hp0)]
    · rcases Nat.lt_or_ge j 2 with hj | hj
      · interval_cases j
        · obtain rfl := h1 (by norm_num)
          simp [hq1, Ne.symm hq1, hp.out.ne_one]
        · obtain rfl := h1 (by norm_num)
          simp [hq1, Ne.symm hq1, hp.out.ne_one]
      · have hn1 : (p ^ 2) ^ j ≠ 1 := fun h => by
          have := hinj (show (p ^ 2) ^ j = (p ^ 2) ^ 0 by rw [h, pow_zero])
          omega
        have hnq : (p ^ 2) ^ j ≠ p ^ 2 := fun h => by
          have := hinj (show (p ^ 2) ^ j = (p ^ 2) ^ 1 by rw [h, pow_one])
          omega
        rw [if_neg hn1, if_neg hnq]
        simp only [add_zero, sub_zero]
        exact dvd_pow_self _ (by omega)
  · have hsum : (∑ i ∈ range (n + 1), if n = (p ^ 2) ^ i then ((p : K') ^ i)⁻¹ else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => if_neg fun h => hn ⟨i, h⟩
    rw [hsum, mul_zero]
    have hn1 : n ≠ 1 := fun h => hn ⟨0, by simp [h]⟩
    have hnq : n ≠ p ^ 2 := fun h => hn ⟨1, by simp [h]⟩
    exact ⟨0, by simp, by simp [hn1, hnq]⟩

private theorem sum_sign_if_eq_pow_at_pow (q : ℕ) (hq : 1 < q) (l : ℕ) :
    (∑ i ∈ range (q ^ l + 1), if q ^ l = q ^ i then ((-1 : ℤ)) ^ i else 0) = (-1) ^ l := by
  have hinj : Function.Injective (fun j : ℕ => q ^ j) := Nat.pow_right_injective (by omega)
  have hlt : l < q ^ l + 1 := by
    have := Nat.lt_pow_self (n := l) hq
    omega
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (hinj h).symm
  · intro hl
    exact absurd (Finset.mem_range.2 hlt) hl

private theorem sum_sign_if_eq_pow_eq_zero_of_ne_pow (q m : ℕ) (hm : ∀ l, m ≠ q ^ l) :
    (∑ i ∈ range (m + 1), if m = q ^ i then ((-1 : ℤ)) ^ i else 0) = 0 :=
  Finset.sum_eq_zero fun i _ => if_neg (hm i)

private theorem sum_sign_if_eq_pow_add_div_eq_indicator_one (q : ℕ) (hq : 1 < q) (n : ℕ) :
    (∑ i ∈ range (n + 1), if n = q ^ i then ((-1 : ℤ)) ^ i else 0) +
      (if q ∣ n then (∑ i ∈ range (n / q + 1), if n / q = q ^ i then ((-1 : ℤ)) ^ i else 0)
        else 0) = if n = 1 then 1 else 0 := by
  have hinj : Function.Injective (fun j : ℕ => q ^ j) := Nat.pow_right_injective (by omega)
  by_cases hn : ∃ l, n = q ^ l
  · obtain ⟨l, rfl⟩ := hn
    rw [sum_sign_if_eq_pow_at_pow q hq l]
    rcases l with _ | l
    · have : ¬ q ∣ 1 := fun h => by have := Nat.le_of_dvd one_pos h; omega
      simp [this]
    · have hd : q ∣ q ^ (l + 1) := dvd_pow_self q (by omega)
      have hdiv : q ^ (l + 1) / q = q ^ l := by
        rw [pow_succ, Nat.mul_div_cancel _ (by omega)]
      have hne : q ^ (l + 1) ≠ 1 := fun h => by
        have := hinj (show q ^ (l + 1) = q ^ 0 by rw [h, pow_zero])
        omega
      rw [if_pos hd, hdiv, sum_sign_if_eq_pow_at_pow q hq l, if_neg hne, pow_succ]
      ring
  · push_neg at hn
    rw [sum_sign_if_eq_pow_eq_zero_of_ne_pow q n hn]
    have hn1 : n ≠ 1 := fun h => hn 0 (by simp [h])
    rw [if_neg hn1, zero_add]
    split_ifs with hd
    · apply sum_sign_if_eq_pow_eq_zero_of_ne_pow
      intro l hl
      apply hn (l + 1)
      rw [pow_succ, ← hl, Nat.div_mul_cancel hd]
    · rfl

private theorem coeff_pow_eq_of_lower_coeff_eq {R : Type} [CommRing R] (a b : PowerSeries R)
    (ha : PowerSeries.X ∣ a) (hb : PowerSeries.X ∣ b) (n : ℕ)
    (hab : ∀ m < n, PowerSeries.coeff m a = PowerSeries.coeff m b) (d : ℕ) (hd : d ≠ 1) :
    PowerSeries.coeff n (a ^ d) = PowerSeries.coeff n (b ^ d) := by
  rcases Nat.lt_or_ge d 2 with h | h
  · interval_cases d
    · simp
    · exact absurd rfl hd
  · have h1 : PowerSeries.X ^ n ∣ a - b := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      rw [map_sub, hab m hm, sub_self]
    have h2 : PowerSeries.X ∣ ∑ i ∈ range d, a ^ i * b ^ (d - 1 - i) := by
      apply Finset.dvd_sum
      intro i hi
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0
        apply Dvd.dvd.mul_left
        exact dvd_pow hb (by omega)
      · exact Dvd.dvd.mul_right (dvd_pow ha (by omega)) _
    have h3 : PowerSeries.X ^ (n + 1) ∣ a ^ d - b ^ d := by
      have he : a ^ d - b ^ d = (a - b) * ∑ i ∈ range d, a ^ i * b ^ (d - 1 - i) := by
        rw [← geom_sum₂_mul]
        ring
      rw [he, pow_succ]
      exact mul_dvd_mul h1 h2
    have h4 := (PowerSeries.X_pow_dvd_iff.1 h3) n (by omega)
    rw [map_sub, sub_eq_zero] at h4
    exact h4

private theorem coeff_subst_eq_sum_coeff_mul_coeff_pow {K : Type} [Field K] (μ f : PowerSeries K)
    (h0 : PowerSeries.constantCoeff μ = 0) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.subst μ f) =
      ∑ d ∈ range (n + 1), PowerSeries.coeff d f * PowerSeries.coeff n (μ ^ d) := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' h0)]
  rw [finsum_eq_sum_of_support_subset _ (s := range (n + 1)) ?_]
  · rfl
  · intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hd
    obtain ⟨r, hr⟩ := PowerSeries.X_dvd_iff.2 h0
    rw [hr, mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega), smul_zero]

theorem sx_mu_alt_int (vp : K') (hvp : vp ^ (p ^ 2 - 1) = (p : K')) (μ : PowerSeries K')
    (h0 : PowerSeries.constantCoeff μ = 0)
    (h1 : (PowerSeries.subst μ (lamF p vp) : PowerSeries K') = PowerSeries.X) (n : ℕ) :
    ∃ y : ℤ, PowerSeries.coeff n μ - PowerSeries.coeff n (altF K' p) = (p : K') * (y : K') := by
  haveI := charZero_K' p K'
  have hp2 : 2 ≤ p := hp.out.two_le
  have hq : 1 < p ^ 2 := by nlinarith
  have hq1 : p ^ 2 ≠ 1 := by omega
  choose z hz1 hz2 using sx_lam_int p K' vp hvp
  have hX : PowerSeries.X ∣ μ := PowerSeries.X_dvd_iff.2 h0
  have hl1 : PowerSeries.coeff 1 (lamF p vp) = 1 := by
    simp [lamF, lgF, Finset.sum_range_succ, Ne.symm hq1, hp.out.ne_one]
  have halt : ∀ m, PowerSeries.coeff m (altF K' p) =
      ((∑ i ∈ range (m + 1), if m = (p ^ 2) ^ i then ((-1 : ℤ)) ^ i else 0 : ℤ) : K') := by
    intro m
    simp only [altF, PowerSeries.coeff_mk]
    push_cast
    rfl
  have hPk : ∀ (Q : Polynomial ℤ) (m : ℕ), PowerSeries.coeff m
      ((Q.map (Int.castRingHom K') : Polynomial K') : PowerSeries K') = (Q.coeff m : K') := by
    intro Q m
    rw [Polynomial.coeff_coe, Polynomial.coeff_map, eq_intCast]
  have hQq : ∀ (R : Polynomial (ZMod p)) (n : ℕ),
      (R ^ (p ^ 2)).coeff n = if p ^ 2 ∣ n then R.coeff (n / p ^ 2) else 0 := by
    intro R n
    rw [sq, pow_mul, ← ZMod.expand_card, ← ZMod.expand_card, ← Polynomial.expand_mul,
      Polynomial.coeff_expand (by positivity)]
  have key : ∀ n, 1 ≤ n → ∃ P : Polynomial ℤ, P.coeff 0 = 0 ∧ (∀ m, n ≤ m → P.coeff m = 0) ∧
      (∀ m < n, PowerSeries.coeff m μ = (P.coeff m : K')) ∧
      (∀ m < n, (p : ℤ) ∣ P.coeff m -
        ∑ i ∈ range (m + 1), if m = (p ^ 2) ^ i then ((-1 : ℤ)) ^ i else 0) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      refine ⟨0, by simp, fun m _ => by simp, fun m hm => ?_, fun m hm => ?_⟩
      · have : m = 0 := by omega
        subst this
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
        simp
      · have : m = 0 := by omega
        subst this
        simp
    | succ n hn ih =>
      obtain ⟨P, hP0, hPz, hPμ, hPd⟩ := ih
      have hXP : PowerSeries.X ∣ ((P.map (Int.castRingHom K') : Polynomial K') : PowerSeries K') := by
        rw [PowerSeries.X_dvd_iff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hPk, hP0,
          Int.cast_zero]
      have hcμ : PowerSeries.coeff n μ = (((if n = 1 then 1 else 0) -
          ∑ d ∈ (range (n + 1)).erase 1, z d * (P ^ d).coeff n : ℤ) : K') := by
        have e1 := congrArg (PowerSeries.coeff n) h1
        rw [coeff_subst_eq_sum_coeff_mul_coeff_pow μ _ h0 n, PowerSeries.coeff_X,
          ← Finset.add_sum_erase _ _ (Finset.mem_range.2 (by omega : 1 < n + 1)),
          hl1, pow_one, one_mul] at e1
        have hS : ∑ d ∈ (range (n + 1)).erase 1,
            PowerSeries.coeff d (lamF p vp) * PowerSeries.coeff n (μ ^ d) =
            ∑ d ∈ (range (n + 1)).erase 1, (z d : K') * ((P ^ d).coeff n : K') := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [hz1 d, coeff_pow_eq_of_lower_coeff_eq μ _ hX hXP n (fun m hm => by rw [hPμ m hm, hPk]) d
            (Finset.ne_of_mem_erase hd), ← Polynomial.coe_pow, ← Polynomial.map_pow, hPk]
        rw [hS] at e1
        simp only [Int.cast_sub, Int.cast_sum, Int.cast_mul, Int.cast_ite, Int.cast_one,
          Int.cast_zero]
        linear_combination e1
      have hcd : (p : ℤ) ∣ ((if n = 1 then 1 else 0) -
          ∑ d ∈ (range (n + 1)).erase 1, z d * (P ^ d).coeff n) -
          ∑ i ∈ range (n + 1), if n = (p ^ 2) ^ i then ((-1 : ℤ)) ^ i else 0 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        have hQ : ∀ m, (P.map (Int.castRingHom (ZMod p))).coeff m = if m < n then
            (((∑ i ∈ range (m + 1), if m = (p ^ 2) ^ i then ((-1 : ℤ)) ^ i else 0 : ℤ)) : ZMod p)
            else 0 := by
          intro m
          rw [Polynomial.coeff_map, eq_intCast]
          split_ifs with hm
          · rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
            exact hPd m hm
          · rw [hPz m (by omega), Int.cast_zero]
        have hzb : ∀ d ∈ (range (n + 1)).erase 1, ((z d : ℤ) : ZMod p) = if d = p ^ 2 then 1 else 0 := by
          intro d hd
          have h := hz2 d
          rw [if_neg (Finset.ne_of_mem_erase hd), zero_add] at h
          split_ifs at h ⊢ with hdq
          · have h' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h
            push_cast at h'
            exact sub_eq_zero.1 h'
          · rw [sub_zero] at h
            exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h
        have hS : ((∑ d ∈ (range (n + 1)).erase 1, z d * (P ^ d).coeff n : ℤ) : ZMod p) =
            if p ^ 2 ∣ n then (((∑ i ∈ range (n / p ^ 2 + 1),
              if n / p ^ 2 = (p ^ 2) ^ i then ((-1 : ℤ)) ^ i else 0 : ℤ)) : ZMod p) else 0 := by
          rw [Int.cast_sum]
          rw [Finset.sum_congr rfl (g := fun d => if d = p ^ 2 then
            ((P.map (Int.castRingHom (ZMod p))) ^ (p ^ 2)).coeff n else 0)]
          · rw [Finset.sum_ite_eq', hQq]
            split_ifs with h1 h2 h2
            · rw [hQ, if_pos (Nat.div_lt_self (by omega) hq)]
            · rfl
            · exfalso
              apply h1
              have := Nat.le_of_dvd (by omega) h2
              rw [Finset.mem_erase, Finset.mem_range]
              exact ⟨hq1, by omega⟩
            · rfl
          · intro d hd
            rw [Int.cast_mul, hzb d hd]
            split_ifs with hdq
            · subst hdq
              rw [one_mul, ← Polynomial.map_pow, Polynomial.coeff_map, eq_intCast]
            · rw [zero_mul]
        have hr := congrArg (Int.cast : ℤ → ZMod p) (sum_sign_if_eq_pow_add_div_eq_indicator_one (p ^ 2) hq n)
        rw [Int.cast_add] at hr
        rw [Int.cast_sub, Int.cast_sub, hS]
        split_ifs at hr ⊢ <;> push_cast at hr ⊢ <;> linear_combination (-1 : ZMod p) * hr
      refine ⟨P + Polynomial.C ((if n = 1 then 1 else 0) -
          ∑ d ∈ (range (n + 1)).erase 1, z d * (P ^ d).coeff n) * Polynomial.X ^ n,
        ?_, ?_, ?_, ?_⟩
      · rw [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, if_neg (by omega), hP0, add_zero]
      · intro m hm
        rw [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, if_neg (by omega), hPz m (by omega),
          add_zero]
      · intro m hm
        rw [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
        rcases Nat.lt_or_ge m n with h | h
        · rw [if_neg (by omega), add_zero]
          exact hPμ m h
        · have hmn : m = n := by omega
          subst hmn
          rw [if_pos rfl, hPz m le_rfl, zero_add]
          exact hcμ
      · intro m hm
        rw [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
        rcases Nat.lt_or_ge m n with h | h
        · rw [if_neg (by omega), add_zero]
          exact hPd m h
        · have hmn : m = n := by omega
          subst hmn
          rw [if_pos rfl, hPz m le_rfl, zero_add]
          exact hcd
  obtain ⟨P, -, -, hPμ, hPd⟩ := key (n + 1) (by omega)
  obtain ⟨y, hy⟩ := hPd n (by omega)
  refine ⟨y, ?_⟩
  rw [hPμ n (by omega), halt n, ← Int.cast_sub, hy]
  push_cast
  ring

theorem sx_mu_alt (vp : K') (hvp : vp ^ (p ^ 2 - 1) = (p : K')) (μ : PowerSeries K')
    (h0 : PowerSeries.constantCoeff μ = 0)
    (h1 : (PowerSeries.subst μ (lamF p vp) : PowerSeries K') = PowerSeries.X) (n : ℕ) :
    ∃ y ∈ Rp p K' vp, PowerSeries.coeff n μ - PowerSeries.coeff n (altF K' p) = (p : K') * y := by
  obtain ⟨y, hy⟩ := sx_mu_alt_int p K' vp hvp μ h0 h1 n
  exact ⟨(y : K'), intCast_mem _ y, hy⟩

end Formalism.MainNotions.FormalGroupSystem.Pf
