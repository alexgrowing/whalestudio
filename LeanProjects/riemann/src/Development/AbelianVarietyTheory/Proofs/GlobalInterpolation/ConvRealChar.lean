import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

noncomputable section

namespace GlobalTheory.Hk.RaySq

variable {K : Type} [Field K] [NumberField K]

def normEq (K : Type) [Field K] [NumberField K] (n : ℕ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset

lemma mem_normEq {n : ℕ} {I : Ideal (𝓞 K)} : I ∈ normEq K n ↔ Ideal.absNorm I = n := by
  simp [normEq]

def dv (C : Ideal (𝓞 K)) : Finset (Ideal (𝓞 K)) :=
  ((Ideal.finite_setOf_absNorm_le (S := 𝓞 K) (Ideal.absNorm C)).toFinset).filter (· ∣ C)

lemma mem_dv {C J : Ideal (𝓞 K)} (hC : C ≠ 0) : J ∈ dv C ↔ J ∣ C := by
  simp only [dv, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, and_iff_right_iff_imp]
  intro h
  have hC' : Ideal.absNorm C ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hC
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hC') (map_dvd Ideal.absNorm h)

def r (f : Ideal (𝓞 K) → ℝ) (C : Ideal (𝓞 K)) : ℝ := ∑ J ∈ dv C, f J

private lemma dvd_of_dvd_prime_pow_mul' {P C J : Ideal (𝓞 K)} (hP : Prime P) (hJ : ¬ P ∣ J) :
    ∀ k : ℕ, J ∣ P ^ k * C → J ∣ C := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro h
    apply ih
    obtain ⟨Y, hY⟩ := h
    have hPY : P ∣ J * Y := ⟨P ^ k * C, by rw [← hY]; ring⟩
    rcases hP.dvd_or_dvd hPY with h1 | ⟨Y', rfl⟩
    · exact absurd h1 hJ
    · refine ⟨Y', ?_⟩
      apply mul_left_cancel₀ hP.ne_zero
      calc P * (P ^ k * C) = P ^ (k + 1) * C := by ring
        _ = J * (P * Y') := hY
        _ = P * (J * Y') := by ring

lemma r_step (f : Ideal (𝓞 K) → ℝ) (hf : ∀ I J, f (I * J) = f I * f J) {P C : Ideal (𝓞 K)} (hP : Prime P) (hC : C ≠ 0)
    (hPC : ¬ P ∣ C) (k : ℕ) : r f (P ^ (k + 1) * C) = f P * r f (P ^ k * C) + r f C := by
  have hP0 : P ≠ 0 := hP.ne_zero
  have hA : P ^ (k + 1) * C ≠ 0 := mul_ne_zero (pow_ne_zero _ hP0) hC
  have hB : P ^ k * C ≠ 0 := mul_ne_zero (pow_ne_zero _ hP0) hC
  have hsplit : dv (P ^ (k + 1) * C) = dv C ∪ (dv (P ^ k * C)).image (P * ·) := by
    ext J
    rw [Finset.mem_union, Finset.mem_image, mem_dv hA, mem_dv hC]
    constructor
    · intro h
      by_cases hJ : P ∣ J
      · right
        obtain ⟨J', rfl⟩ := hJ
        refine ⟨J', (mem_dv hB).2 ?_, rfl⟩
        obtain ⟨Y, hY⟩ := h
        refine ⟨Y, mul_left_cancel₀ hP0 ?_⟩
        calc P * (P ^ k * C) = P ^ (k + 1) * C := by ring
          _ = P * J' * Y := hY
          _ = P * (J' * Y) := by ring
      · left
        exact dvd_of_dvd_prime_pow_mul' hP hJ (k + 1) h
    · rintro (h | ⟨J', hJ', rfl⟩)
      · exact h.trans ⟨P ^ (k + 1), by ring⟩
      · rw [mem_dv hB] at hJ'
        have e : P * (P ^ k * C) = P ^ (k + 1) * C := by ring
        rw [← e]
        exact mul_dvd_mul_left P hJ'
  have hdisj : Disjoint (dv C) ((dv (P ^ k * C)).image (P * ·)) := by
    rw [Finset.disjoint_left]
    intro J hJ hJ'
    rw [mem_dv hC] at hJ
    obtain ⟨J', -, rfl⟩ := Finset.mem_image.1 hJ'
    exact hPC ((dvd_mul_right P J').trans hJ)
  unfold r
  rw [hsplit, Finset.sum_union hdisj, Finset.sum_image (fun a _ b _ hab => mul_left_cancel₀ hP0 hab)]
  simp only [hf, ← Finset.mul_sum]
  ring

lemma r_pow (f : Ideal (𝓞 K) → ℝ) (hf : ∀ I J, f (I * J) = f I * f J) {P C : Ideal (𝓞 K)} (hP : Prime P) (hC : C ≠ 0)
    (hPC : ¬ P ∣ C) (k : ℕ) : r f (P ^ k * C) = (∑ i ∈ Finset.range (k + 1), f P ^ i) * r f C := by
  have hg : ∀ m : ℕ, ∑ i ∈ Finset.range (m + 1), f P ^ i = f P * ∑ i ∈ Finset.range m, f P ^ i + 1 := by
    intro m
    rw [Finset.sum_range_succ', Finset.mul_sum]
    simp only [pow_succ', pow_zero]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [r_step f hf hP hC hPC k, ih, hg (k + 1)]
    ring

private lemma sum_range_neg_one_pow_eq_ite (n : ℕ) :
    ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i = if Even n then 0 else 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : Even n
    · have h' : ¬ Even (n + 1) := by rw [Nat.even_add_one]; exact not_not.2 h
      rw [if_pos h, if_neg h', h.neg_one_pow]
      norm_num
    · have h' : Even (n + 1) := Nat.even_add_one.2 h
      rw [if_neg h, if_pos h', (Nat.not_even_iff_odd.1 h).neg_one_pow]
      norm_num

lemma geom_bounds {x : ℝ} (hx : x = 0 ∨ x = 1 ∨ x = -1) (k : ℕ) :
    0 ≤ ∑ i ∈ Finset.range (k + 1), x ^ i ∧ 1 ≤ ∑ i ∈ Finset.range (2 * k + 1), x ^ i := by
  rcases hx with rfl | rfl | rfl
  · simp [Finset.sum_range_succ']
  · simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    refine ⟨by positivity, ?_⟩
    push_cast
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  · rw [sum_range_neg_one_pow_eq_ite, sum_range_neg_one_pow_eq_ite]
    have h : ¬ Even (2 * k + 1) := by
      rw [Nat.even_add_one, not_not]
      exact even_two_mul k
    rw [if_neg h]
    refine ⟨?_, le_refl _⟩
    split_ifs <;> norm_num

lemma r_one (f : Ideal (𝓞 K) → ℝ) (h1 : f 1 = 1) : r f 1 = 1 := by
  have hd : dv (1 : Ideal (𝓞 K)) = {1} := by
    ext J
    rw [mem_dv one_ne_zero, Finset.mem_singleton, Ideal.dvd_iff_le, Ideal.one_eq_top, top_le_iff]
  unfold r
  rw [hd, Finset.sum_singleton, h1]

lemma r_bounds (f : Ideal (𝓞 K) → ℝ) (h1 : f 1 = 1) (hf : ∀ I J, f (I * J) = f I * f J)
    (hv : ∀ I, f I = 0 ∨ f I = 1 ∨ f I = -1) (C : Ideal (𝓞 K)) (hC : C ≠ 0) : 0 ≤ r f C ∧ 1 ≤ r f (C ^ 2) := by
  suffices h : ∀ N : ℕ, ∀ C : Ideal (𝓞 K), C ≠ 0 → Ideal.absNorm C = N →
      0 ≤ r f C ∧ 1 ≤ r f (C ^ 2) from h _ C hC rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro C hC hN
  by_cases hu : IsUnit C
  · obtain rfl : C = 1 := isUnit_iff_eq_one.1 hu
    rw [one_pow, r_one f h1]
    norm_num
  · obtain ⟨P, hPirr, hPC⟩ := WfDvdMonoid.exists_irreducible_factor hu hC
    have hP : Prime P := UniqueFactorizationMonoid.irreducible_iff_prime.1 hPirr
    obtain ⟨k, D, hPD, rfl⟩ := WfDvdMonoid.max_power_factor hC hPirr
    have hD : D ≠ 0 := by
      rintro rfl
      exact hC (mul_zero _)
    have hk : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, one_mul] at hPC
      exact hPD hPC
    have hN2 : 2 ≤ Ideal.absNorm P := by
      have h0 : Ideal.absNorm P ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]
        exact hP.ne_zero
      have h1' : Ideal.absNorm P ≠ 1 := by
        rw [Ne, Ideal.absNorm_eq_one_iff]
        intro h
        apply hPirr.not_isUnit
        rw [h, ← Ideal.one_eq_top]
        exact isUnit_one
      omega
    have hD0 : 0 < Ideal.absNorm D := by
      apply Nat.pos_of_ne_zero
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact hD
    have hlt : Ideal.absNorm D < N := by
      rw [← hN, map_mul, map_pow]
      have h2 : 2 ≤ Ideal.absNorm P ^ k := le_trans hN2 (Nat.le_self_pow hk _)
      nlinarith
    obtain ⟨ihD1, ihD2⟩ := ih _ hlt D hD rfl
    have hPD2 : ¬ P ∣ D ^ 2 := by
      rw [pow_two]
      intro h
      rcases hP.dvd_or_dvd h with h | h <;> exact hPD h
    have hD2 : D ^ 2 ≠ 0 := pow_ne_zero _ hD
    obtain ⟨g1, g2⟩ := geom_bounds (hv P) k
    constructor
    · rw [r_pow f hf hP hD hPD k]
      exact mul_nonneg g1 ihD1
    · have e : (P ^ k * D) ^ 2 = P ^ (2 * k) * D ^ 2 := by ring
      rw [e, r_pow f hf hP hD2 hPD2 (2 * k)]
      exact one_le_mul_of_one_le_of_one_le g2 ihD2

lemma conv_eq (F : Ideal (𝓞 K) → Ideal (𝓞 K) → ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∑ p ∈ n.divisorsAntidiagonal, ∑ I ∈ normEq K p.1, ∑ J ∈ normEq K p.2, F (I * J) J =
      ∑ C ∈ normEq K n, ∑ J ∈ dv C, F C J := by
  have L : (∑ p ∈ n.divisorsAntidiagonal, ∑ I ∈ normEq K p.1, ∑ J ∈ normEq K p.2, F (I * J) J) =
      ∑ y ∈ n.divisorsAntidiagonal.sigma (fun p => normEq K p.1 ×ˢ normEq K p.2),
        F (y.2.1 * y.2.2) y.2.2 := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_product]
  have R : (∑ C ∈ normEq K n, ∑ J ∈ dv C, F C J) =
      ∑ y ∈ (normEq K n).sigma (fun C => dv C), F y.1 y.2 := by
    rw [Finset.sum_sigma]
  rw [L, R]
  refine Finset.sum_nbij'
    (fun y : (Σ _ : ℕ × ℕ, Ideal (𝓞 K) × Ideal (𝓞 K)) =>
      (⟨y.2.1 * y.2.2, y.2.2⟩ : Σ _ : Ideal (𝓞 K), Ideal (𝓞 K)))
    (fun y : (Σ _ : Ideal (𝓞 K), Ideal (𝓞 K)) =>
      (⟨(Ideal.absNorm y.1 / Ideal.absNorm y.2, Ideal.absNorm y.2),
        ((if h : y.2 ∣ y.1 then Exists.choose h else 0), y.2)⟩ :
        Σ _ : ℕ × ℕ, Ideal (𝓞 K) × Ideal (𝓞 K))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨a, b⟩, I, J⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_product, Nat.mem_divisorsAntidiagonal, mem_normEq] at hy ⊢
    obtain ⟨⟨hab, -⟩, hI, hJ⟩ := hy
    have hIJ0 : I * J ≠ 0 := by
      intro h
      have e := congrArg Ideal.absNorm h
      rw [map_mul, _root_.map_zero, hI, hJ, hab] at e
      exact hn e
    exact ⟨by rw [map_mul, hI, hJ, hab], (mem_dv hIJ0).2 (dvd_mul_left J I)⟩
  · rintro ⟨C, J⟩ hy
    simp only [Finset.mem_sigma, mem_normEq] at hy
    obtain ⟨hCn, hJ⟩ := hy
    have hC0 : C ≠ 0 := by
      rintro rfl
      rw [_root_.map_zero] at hCn
      exact hn hCn.symm
    obtain ⟨c, rfl⟩ := (mem_dv hC0).1 hJ
    have hJ0 : J ≠ 0 := by
      rintro rfl
      exact hC0 (zero_mul c)
    have hch : (if h : J ∣ J * c then Exists.choose h else 0) = c := by
      rw [dif_pos (dvd_mul_right J c)]
      exact mul_left_cancel₀ hJ0 (Exists.choose_spec (dvd_mul_right J c)).symm
    have hNJ : 0 < Ideal.absNorm J := by
      apply Nat.pos_of_ne_zero
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact hJ0
    simp only [Finset.mem_sigma, Finset.mem_product, Nat.mem_divisorsAntidiagonal, mem_normEq]
    rw [hch, map_mul, Nat.mul_div_cancel_left _ hNJ]
    rw [map_mul] at hCn
    exact ⟨⟨by rw [mul_comm]; exact hCn, hn⟩, rfl, trivial⟩
  · rintro ⟨⟨a, b⟩, I, J⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_product, Nat.mem_divisorsAntidiagonal, mem_normEq] at hy
    obtain ⟨⟨hab, -⟩, hI, hJ⟩ := hy
    have hJ0 : J ≠ 0 := by
      rintro rfl
      rw [_root_.map_zero] at hJ
      subst hJ
      exact hn (by rw [← hab, mul_zero])
    have hNJ : 0 < Ideal.absNorm J := by
      apply Nat.pos_of_ne_zero
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact hJ0
    have hch : (if h : J ∣ I * J then Exists.choose h else 0) = I := by
      rw [dif_pos (dvd_mul_left J I)]
      apply mul_left_cancel₀ hJ0
      rw [← Exists.choose_spec (dvd_mul_left J I), mul_comm]
    dsimp only
    rw [hch, map_mul, Nat.mul_div_cancel _ hNJ, hI, hJ]
  · rintro ⟨C, J⟩ hy
    simp only [Finset.mem_sigma, mem_normEq] at hy
    obtain ⟨hCn, hJ⟩ := hy
    have hC0 : C ≠ 0 := by
      rintro rfl
      rw [_root_.map_zero] at hCn
      exact hn hCn.symm
    obtain ⟨c, rfl⟩ := (mem_dv hC0).1 hJ
    have hJ0 : J ≠ 0 := by
      rintro rfl
      exact hC0 (zero_mul c)
    have hch : (if h : J ∣ J * c then Exists.choose h else 0) = c := by
      rw [dif_pos (dvd_mul_right J c)]
      exact mul_left_cancel₀ hJ0 (Exists.choose_spec (dvd_mul_right J c)).symm
    dsimp only
    rw [hch, mul_comm]
  · rintro ⟨p, I, J⟩ _
    rfl

variable {M : ℕ} (D : RayData K M)

def chi (ε : D.G → ℝ) (I : Ideal (𝓞 K)) : ℝ :=
  if I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)}) then ε (D.cls I) else 0

lemma sum_aRay (ε : D.G → ℝ) (n : ℕ) : ∑ g, ε g * aRay D g n = ∑ I ∈ normEq K n, chi D ε I := by
  have hcard : ∀ g, aRay D g n = (((normEq K n).filter (fun I =>
      (I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)})) ∧ D.cls I = g)).card : ℝ) := by
    intro g
    unfold aRay
    congr 1
    rw [← Set.ncard_coe_finset]
    congr 1
    ext I
    simp only [idealsIn, Finset.coe_filter, Set.mem_setOf_eq, mem_normEq]
    tauto
  have hchi : ∀ I, chi D ε I = ∑ g, if (I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)})) ∧ D.cls I = g
      then ε g else 0 := by
    intro I
    by_cases h : I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)})
    · rw [chi, if_pos h]
      simp only [ite_and, if_pos h]
      simp
    · rw [chi, if_neg h]
      simp only [ite_and, if_neg h, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl (fun I _ => hchi I), Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcard g, mul_comm]

lemma chi_mul (ε : D.G → ℝ) (hε : ∀ g h, ε (g * h) = ε g * ε h) (I J : Ideal (𝓞 K)) :
    chi D ε (I * J) = chi D ε I * chi D ε J := by
  by_cases hI : I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)})
  · by_cases hJ : J ≠ ⊥ ∧ IsCoprime J (Ideal.span {(M : 𝓞 K)})
    · have hIJ : I * J ≠ ⊥ ∧ IsCoprime (I * J) (Ideal.span {(M : 𝓞 K)}) :=
        ⟨mul_ne_zero hI.1 hJ.1, hI.2.mul_left hJ.2⟩
      simp only [chi]
      rw [if_pos hIJ, if_pos hI, if_pos hJ, D.cls_mul I J hI.2 hJ.2 hI.1 hJ.1, hε]
    · have hIJ : ¬ (I * J ≠ ⊥ ∧ IsCoprime (I * J) (Ideal.span {(M : 𝓞 K)})) := by
        rintro ⟨h1, h2⟩
        exact hJ ⟨fun h => h1 (by rw [h, Ideal.mul_bot]), h2.of_mul_left_right⟩
      simp only [chi]
      rw [if_pos hI, if_neg hJ, if_neg hIJ, mul_zero]
  · have hIJ : ¬ (I * J ≠ ⊥ ∧ IsCoprime (I * J) (Ideal.span {(M : 𝓞 K)})) := by
      rintro ⟨h1, h2⟩
      exact hI ⟨fun h => h1 (by rw [h, Ideal.bot_mul]), h2.of_mul_left_left⟩
    simp only [chi]
    rw [if_neg hI, if_neg hIJ, zero_mul]

lemma chi_one (ε : D.G → ℝ) (h1 : ε 1 = 1) : chi D ε 1 = 1 := by
  have hc : IsCoprime (1 : Ideal (𝓞 K)) (Ideal.span {(M : 𝓞 K)}) := isCoprime_one_left
  have hb : (1 : Ideal (𝓞 K)) ≠ ⊥ := by
    rw [Ideal.one_eq_top]
    exact top_ne_bot
  have hcls : D.cls 1 = 1 := by
    have e := D.cls_mul 1 1 hc hc hb hb
    rw [one_mul] at e
    exact mul_left_cancel (by rw [mul_one]; exact e.symm : D.cls 1 * D.cls 1 = D.cls 1 * 1)
  rw [chi, if_pos ⟨hb, hc⟩, hcls, h1]

lemma conv_aRay (ε : D.G → ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∑ p ∈ n.divisorsAntidiagonal, (∑ g, aRay D g p.1) * ∑ g, ε g * aRay D g p.2 =
      ∑ C ∈ normEq K n, chi D (fun _ => 1) C * r (chi D ε) C := by
  have h1 : ∀ m, ∑ g, aRay D g m = ∑ I ∈ normEq K m, chi D (fun _ => 1) I := by
    intro m
    rw [← sum_aRay D (fun _ => 1) m]
    simp
  have hkey : ∀ I J : Ideal (𝓞 K),
      chi D (fun _ => 1) I * chi D ε J = chi D (fun _ => 1) (I * J) * chi D ε J := by
    intro I J
    rw [chi_mul D (fun _ => 1) (fun _ _ => (mul_one 1).symm) I J, mul_assoc]
    congr 1
    simp only [chi]
    split_ifs <;> simp
  calc _ = ∑ p ∈ n.divisorsAntidiagonal, ∑ I ∈ normEq K p.1, ∑ J ∈ normEq K p.2,
        chi D (fun _ => 1) (I * J) * chi D ε J := by
        simp_rw [h1, sum_aRay D ε, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun I _ =>
          Finset.sum_congr rfl fun J _ => hkey I J
    _ = _ := (conv_eq (fun C J => chi D (fun _ => 1) C * chi D ε J) hn).trans
        (by simp only [r, Finset.mul_sum])

theorem conv_real_char : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (ε : D.G → ℝ), ε 1 = 1 → (∀ g h, ε (g * h) = ε g * ε h) → (∀ g, ε g = 1 ∨ ε g = -1) → ∀ n : ℕ, 0 ≤ ∑ p ∈ n.divisorsAntidiagonal, (∑ g, aRay D g p.1) * ∑ g, ε g * aRay D g p.2 ∧ ∑ g, aRay D g n ≤ ∑ p ∈ (n ^ 2).divisorsAntidiagonal, (∑ g, aRay D g p.1) * ∑ g, ε g * aRay D g p.2 := by
  intro K _ _ M _ D ε h1 hmul hpm n
  have hv : ∀ I, chi D ε I = 0 ∨ chi D ε I = 1 ∨ chi D ε I = -1 := by
    intro I
    unfold chi
    split_ifs
    · rcases hpm (D.cls I) with h | h <;> simp [h]
    · simp
  have hr : ∀ C : Ideal (𝓞 K), C ≠ 0 → 0 ≤ r (chi D ε) C ∧ 1 ≤ r (chi D ε) (C ^ 2) :=
    fun C hC => r_bounds (chi D ε) (chi_one D ε h1) (chi_mul D ε hmul) hv C hC
  have h01 : ∀ I, chi D (fun _ => 1) I =
      if I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)}) then 1 else 0 := fun I => rfl
  have hterm : ∀ C : Ideal (𝓞 K), 0 ≤ chi D (fun _ => 1) C * r (chi D ε) C := by
    intro C
    rw [h01]
    split_ifs with h
    · rw [one_mul]
      exact (hr C h.1).1
    · rw [zero_mul]
  have hsum1 : ∀ m, ∑ g, aRay D g m = ∑ I ∈ normEq K m, chi D (fun _ => 1) I := by
    intro m
    rw [← sum_aRay D (fun _ => 1) m]
    simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨by simp, ?_⟩
    have h0 : ∑ I ∈ normEq K 0, chi D (fun _ => 1) I = 0 := by
      refine Finset.sum_eq_zero fun I hI => ?_
      rw [mem_normEq, Ideal.absNorm_eq_zero_iff] at hI
      simp [chi, hI]
    rw [hsum1, h0]
    simp
  · have hn0 : n ≠ 0 := hn.ne'
    rw [conv_aRay D ε hn0, conv_aRay D ε (pow_ne_zero 2 hn0), hsum1]
    refine ⟨Finset.sum_nonneg fun C _ => hterm C, ?_⟩
    calc ∑ I ∈ normEq K n, chi D (fun _ => 1) I
        ≤ ∑ I ∈ normEq K n, chi D (fun _ => 1) (I ^ 2) * r (chi D ε) (I ^ 2) := by
          refine Finset.sum_le_sum fun I _ => ?_
          by_cases h : I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)})
          · have h2 : I ^ 2 ≠ ⊥ ∧ IsCoprime (I ^ 2) (Ideal.span {(M : 𝓞 K)}) :=
              ⟨pow_ne_zero 2 h.1, h.2.pow_left⟩
            rw [h01, h01, if_pos h, if_pos h2, one_mul]
            exact (hr I h.1).2
          · rw [h01 I, if_neg h]
            exact hterm (I ^ 2)
      _ = ∑ C ∈ (normEq K n).image (· ^ 2), chi D (fun _ => 1) C * r (chi D ε) C := by
          rw [Finset.sum_image]
          intro a _ b _ hab
          have hab' : a ^ 2 = b ^ 2 := hab
          exact dvd_antisymm ((UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd two_ne_zero).1 hab'.dvd)
            ((UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd two_ne_zero).1 hab'.symm.dvd)
      _ ≤ ∑ C ∈ normEq K (n ^ 2), chi D (fun _ => 1) C * r (chi D ε) C := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun C _ _ => hterm C
          intro C hC
          obtain ⟨I, hI, rfl⟩ := Finset.mem_image.1 hC
          rw [mem_normEq] at hI ⊢
          rw [map_pow, hI]

end GlobalTheory.Hk.RaySq

end
