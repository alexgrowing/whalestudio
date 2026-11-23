import Mathlib

namespace Formalism.MainNotions.N.Ln34

open Finset

section GradNPfVal

variable {L O : Type*} [Field L] [CommRing O] (v : AddValuation L (WithTop ℚ)) (ι : O →+* L)
  (hι : Function.Injective ι) (hR : ∀ x : L, 0 ≤ v x ↔ ∃ a : O, ι a = x)

include hR in
theorem gradNPf_v_nonneg (a : O) : 0 ≤ v (ι a) := (hR (ι a)).2 ⟨a, rfl⟩

include hι hR in
theorem gradNPf_isUnit_of_v (a : O) (ha : v (ι a) = 0) : IsUnit a := by
  have hne : ι a ≠ 0 := by
    intro h0
    rw [h0, v.map_zero] at ha
    first
      | simp at ha
      | exact WithTop.top_ne_zero ha
      | exact absurd ha (by decide)
  have hinv : v (ι a)⁻¹ = 0 := by
    have h1 : v (ι a * (ι a)⁻¹) = 0 := by rw [mul_inv_cancel₀ hne, v.map_one]
    rwa [v.map_mul, ha, zero_add] at h1
  obtain ⟨b, hb⟩ := (hR _).1 (le_of_eq hinv.symm)
  have hab : a * b = 1 := hι (by rw [_root_.map_mul, _root_.map_one, hb, mul_inv_cancel₀ hne])
  first
    | exact isUnit_iff_exists_inv.2 ⟨b, hab⟩
    | exact IsUnit.of_mul_eq_one b hab
    | exact isUnit_of_mul_eq_one_right hab

private theorem exists_one_add_pow_eq_one_add_mul_add_sq (a : O) (i : ℕ) :
    ∃ b : O, (1 + a) ^ i = 1 + (i : O) * a + a ^ 2 * b := by
  induction i with
  | zero => exact ⟨0, by simp⟩
  | succ i ih =>
    obtain ⟨b, hb⟩ := ih
    exact ⟨(i : O) + b + b * a, by rw [pow_succ, hb]; push_cast; ring⟩

private theorem exists_geom_sum_one_add_eq_natCast_add_mul (a : O) (n : ℕ) :
    ∃ C : O, ∑ i ∈ range n, (1 + a) ^ i = (n : O) + a * C := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨C, hC⟩ := ih
    obtain ⟨b, hb⟩ := exists_one_add_pow_eq_one_add_mul_add_sq a n
    exact ⟨C + n + a * b, by rw [sum_range_succ, hC, hb]; push_cast; ring⟩

private theorem exists_geom_sum_one_add_eq_second_order (a : O) (n : ℕ) :
    ∃ B : O, ∑ i ∈ range n, (1 + a) ^ i =
      (n : O) + a * ((∑ i ∈ range n, i : ℕ) : O) + a ^ 2 * B := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨B, hB⟩ := ih
    obtain ⟨b, hb⟩ := exists_one_add_pow_eq_one_add_mul_add_sq a n
    refine ⟨B + b, ?_⟩
    simp only [sum_range_succ]
    rw [hB, hb]
    push_cast
    ring

private theorem val_add_eq_left_of_val_lt (x y : L) (h : v x < v y) : v (x + y) = v x := by
  have h1 : min (v x) (v y) ≤ v (x + y) := v.map_add x y
  rw [min_eq_left h.le] at h1
  refine le_antisymm ?_ h1
  by_contra hc
  push_neg at hc
  have h2 : min (v (x + y)) (v (-y)) ≤ v (x + y + -y) := v.map_add _ _
  have e : x + y + -y = x := by ring
  rw [e, v.map_neg] at h2
  exact lt_irrefl _ (lt_of_lt_of_le (lt_min hc h) h2)

theorem gradNPf_zero_lt_one : (0 : WithTop ℚ) < 1 := by
  first
    | exact WithTop.coe_lt_coe.2 zero_lt_one
    | exact_mod_cast (zero_lt_one : (0 : ℚ) < 1)
    | norm_num
    | simp

include hι hR in
theorem gradNPf_unit_one_add (lO d : O) (hl : v (ι lO) = 1) : IsUnit (1 + lO * d) := by
  apply gradNPf_isUnit_of_v v ι hι hR
  have h0 : 0 ≤ v (ι d) := gradNPf_v_nonneg v ι hR d
  have hy : v (ι lO * ι d) = 1 + v (ι d) := by rw [v.map_mul, hl]
  have hle : (1 : WithTop ℚ) ≤ 1 + v (ι d) := by
    first
      | exact le_add_of_nonneg_right h0
      | simpa using add_le_add_left h0 1
  have hlt : v (1 : L) < v (ι lO * ι d) := by
    rw [v.map_one, hy]
    exact lt_of_lt_of_le gradNPf_zero_lt_one hle
  rw [_root_.map_add, _root_.map_one, _root_.map_mul, val_add_eq_left_of_val_lt v _ _ hlt, v.map_one]

include hι hR in
theorem gradNPf_unit_nat (l : ℕ) (hp : l.Prime) (hl : v (l : L) = 1) (m : ℕ) (hm : ¬ l ∣ m) :
    IsUnit (m : O) := by
  have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  have hb : ((Nat.gcd l m : ℕ) : ℤ) = (l : ℤ) * Nat.gcdA l m + (m : ℤ) * Nat.gcdB l m :=
    Nat.gcd_eq_gcd_ab l m
  rw [show Nat.gcd l m = 1 from hcop] at hb
  have hO : (m : O) * ((Nat.gcdB l m : ℤ) : O) = 1 + (l : O) * (-((Nat.gcdA l m : ℤ) : O)) := by
    have h := congrArg (fun z : ℤ => (z : O)) hb
    push_cast at h
    linear_combination -1 * h
  have hlO : v (ι (l : O)) = 1 := by rw [_root_.map_natCast]; exact hl
  have hu := gradNPf_unit_one_add v ι hι hR (l : O) (-((Nat.gcdA l m : ℤ) : O)) hlO
  rw [← hO] at hu
  exact isUnit_of_mul_isUnit_left hu

include hι hR in
theorem gradNPf_sub_one (lO x : O) (hl : v (ι lO) = 1) (hx : v (ι x - 1) = 1) :
    ∃ t : O, IsUnit t ∧ x - 1 = lO * t := by
  have hne : ι lO ≠ 0 := by
    intro h0
    rw [h0, v.map_zero] at hl
    first
      | simp at hl
      | exact WithTop.top_ne_one hl
      | exact absurd hl (by decide)
  have hinv : 1 + v (ι lO)⁻¹ = 0 := by
    have h1 : v (ι lO * (ι lO)⁻¹) = 0 := by rw [mul_inv_cancel₀ hne, v.map_one]
    rwa [v.map_mul, hl] at h1
  have hq : v ((ι x - 1) * (ι lO)⁻¹) = 0 := by
    rw [v.map_mul, hx, hinv]
  obtain ⟨t, ht⟩ := (hR _).1 (le_of_eq hq.symm)
  refine ⟨t, gradNPf_isUnit_of_v v ι hι hR t (by rw [ht, hq]), hι ?_⟩
  rw [_root_.map_sub, _root_.map_one, _root_.map_mul, ht, mul_comm (ι lO), mul_assoc,
    inv_mul_cancel₀ hne, mul_one]

include hι hR in

theorem gradNPf_lte (l : ℕ) [hp : Fact l.Prime] (hl2 : l ≠ 2) (hl : v (l : L) = 1)
    (x t : O) (ht : IsUnit t) (hxt : x - 1 = (l : O) * t) :
    ∀ m : ℕ, m ≠ 0 → ∃ ε : O, IsUnit ε ∧ x ^ m - 1 = (l : O) ^ (1 + padicValNat l m) * ε := by
  have lte_isUnit_add_mul_lemma_5 {L : Type _} {O : Type _} [Field L] [CommRing O] (v : AddValuation L (WithTop ℚ)) (ι : O →+* L) (hinj : Function.Injective ι)
      (hRR : ∀ x : L, 0 ≤ v x ↔ ∃ a : O, ι a = x) (lO s c : O) (hl : v (ι lO) = 1)
      (hs : IsUnit s) : IsUnit (s + lO * c) := by
    obtain ⟨u, rfl⟩ := hs
    have h : (u : O) + lO * c = u * (1 + lO * (c * ↑u⁻¹)) := by
      linear_combination (-(lO * c)) * Units.mul_inv u
    rw [h]
    exact u.isUnit.mul (gradNPf_unit_one_add v ι hinj hRR lO _ hl)
  have lte_pow_coprime_step_lemma_6 {L : Type _} {O : Type _} [Field L] [CommRing O] (v : AddValuation L (WithTop ℚ)) (ι : O →+* L) (hinj : Function.Injective ι)
      (hRR : ∀ x : L, 0 ≤ v x ↔ ∃ a : O, ι a = x) (l : ℕ) [hp : Fact l.Prime]
      (hl : v (l : L) = 1) (x t : O) (ht : IsUnit t) (hxt : x - 1 = (l : O) * t) (s : ℕ)
      (hs : ¬ l ∣ s) : ∃ ε : O, IsUnit ε ∧ x ^ s - 1 = (l : O) * ε := by
    have hlO : v (ι (l : O)) = 1 := by rw [_root_.map_natCast]; exact hl
    obtain ⟨C, hC⟩ := exists_geom_sum_one_add_eq_natCast_add_mul (x - 1) s
    have e : 1 + (x - 1) = x := by ring
    rw [e, hxt] at hC
    have hsu : IsUnit (s : O) := gradNPf_unit_nat v ι hinj hRR l hp.out hl s hs
    refine ⟨t * ((s : O) + (l : O) * (t * C)),
      ht.mul (lte_isUnit_add_mul_lemma_5 v ι hinj hRR _ _ _ hlO hsu), ?_⟩
    rw [← geom_sum_mul, hC, hxt]
    ring
  have lte_pow_prime_step_lemma_7 {L : Type _} {O : Type _} [Field L] [CommRing O] (v : AddValuation L (WithTop ℚ)) (ι : O →+* L) (hinj : Function.Injective ι)
      (hRR : ∀ x : L, 0 ≤ v x ↔ ∃ a : O, ι a = x) (l : ℕ) [hp : Fact l.Prime] (hl2 : l ≠ 2)
      (hl : v (l : L) = 1) (y u : O) (hu : IsUnit u) (j : ℕ)
      (hyu : y - 1 = (l : O) ^ (j + 1) * u) :
      ∃ ε : O, IsUnit ε ∧ y ^ l - 1 = (l : O) ^ (j + 2) * ε := by
    have hlO : v (ι (l : O)) = 1 := by rw [_root_.map_natCast]; exact hl
    obtain ⟨k, hk⟩ : ∃ k, l = 2 * k + 1 := by
      rcases hp.out.eq_two_or_odd' with h | h
      · exact absurd h hl2
      · obtain ⟨k, hk⟩ := h
        exact ⟨k, hk⟩
    have hsum : (∑ i ∈ range l, i) = l * k := by
      have h2 : (∑ i ∈ range l, i) * 2 = l * (l - 1) := sum_range_id_mul_two l
      have h3 : l - 1 = 2 * k := by omega
      rw [h3] at h2
      apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by norm_num)
      rw [h2]
      ring
    obtain ⟨B, hB⟩ := exists_geom_sum_one_add_eq_second_order (y - 1) l
    have e : 1 + (y - 1) = y := by ring
    rw [e, hsum, hyu] at hB
    refine ⟨u * (1 + (l : O) * ((l : O) ^ j * u * (k : O) + ((l : O) ^ j) ^ 2 * u ^ 2 * B)),
      hu.mul (gradNPf_unit_one_add v ι hinj hRR _ _ hlO), ?_⟩
    rw [← geom_sum_mul, hB, hyu]
    push_cast
    ring
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases hdvd : l ∣ m
    · obtain ⟨m', rfl⟩ := hdvd
      have hm' : m' ≠ 0 := by
        rintro rfl
        exact hm (mul_zero l)
      have hl1 : 1 < l := hp.out.one_lt
      have hlt : m' < l * m' := by
        have hpos : 0 < m' := Nat.pos_of_ne_zero hm'
        nlinarith
      obtain ⟨ε, hε, he⟩ := ih m' hlt hm'
      obtain ⟨ε', hε', he'⟩ := lte_pow_prime_step_lemma_7 v ι hι hR l hl2 hl (x ^ m') ε hε
        (padicValNat l m') (by rw [he]; ring)
      have hv : padicValNat l (l * m') = padicValNat l m' + 1 := by
        rw [padicValNat.mul hp.out.ne_zero hm']
        first
          | rw [padicValNat_self]; ring
          | rw [padicValNat.self hl1]; ring
          | simp; ring
          | simp
      refine ⟨ε', hε', ?_⟩
      rw [hv, show l * m' = m' * l from Nat.mul_comm l m', pow_mul, he']
      ring
    · obtain ⟨ε, hε, he⟩ := lte_pow_coprime_step_lemma_6 v ι hι hR l hl x t ht hxt m hdvd
      refine ⟨ε, hε, ?_⟩
      rw [padicValNat.eq_zero_of_not_dvd hdvd, he]
      ring

theorem gradNPf_sum_val (l : ℕ) [hp : Fact l.Prime] (N : ℕ) :
    ∑ y ∈ Ico 1 (N + 1), (1 + padicValNat l y) = N + padicValNat l N.factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Ico_succ_top (by omega : 1 ≤ N + 1), ih, Nat.factorial_succ,
      padicValNat.mul (Nat.succ_ne_zero N) (Nat.factorial_ne_zero N)]
    ring

include hι hR in

theorem gradNPf_prod (l : ℕ) [hp : Fact l.Prime] (hl2 : l ≠ 2) (hl : v (l : L) = 1)
    (x t : O) (ht : IsUnit t) (hxt : x - 1 = (l : O) * t) (s : ℕ) (hs : s ≠ 0) (hsl : ¬ l ∣ s)
    (N : ℕ) : ∃ a : O, (l : O) ^ (N + padicValNat l N.factorial) =
      a * ∏ y ∈ Ico 1 (N + 1), ((x ^ s) ^ y - 1) := by
  have lte_isUnit_add_mul_lemma_5 {L : Type _} {O : Type _} [Field L] [CommRing O] (v : AddValuation L (WithTop ℚ)) (ι : O →+* L) (hinj : Function.Injective ι)
      (hRR : ∀ x : L, 0 ≤ v x ↔ ∃ a : O, ι a = x) (lO s c : O) (hl : v (ι lO) = 1)
      (hs : IsUnit s) : IsUnit (s + lO * c) := by
    obtain ⟨u, rfl⟩ := hs
    have h : (u : O) + lO * c = u * (1 + lO * (c * ↑u⁻¹)) := by
      linear_combination (-(lO * c)) * Units.mul_inv u
    rw [h]
    exact u.isUnit.mul (gradNPf_unit_one_add v ι hinj hRR lO _ hl)
  have lte_pow_coprime_step_lemma_6 {L : Type _} {O : Type _} [Field L] [CommRing O] (v : AddValuation L (WithTop ℚ)) (ι : O →+* L) (hinj : Function.Injective ι)
      (hRR : ∀ x : L, 0 ≤ v x ↔ ∃ a : O, ι a = x) (l : ℕ) [hp : Fact l.Prime]
      (hl : v (l : L) = 1) (x t : O) (ht : IsUnit t) (hxt : x - 1 = (l : O) * t) (s : ℕ)
      (hs : ¬ l ∣ s) : ∃ ε : O, IsUnit ε ∧ x ^ s - 1 = (l : O) * ε := by
    have hlO : v (ι (l : O)) = 1 := by rw [_root_.map_natCast]; exact hl
    obtain ⟨C, hC⟩ := exists_geom_sum_one_add_eq_natCast_add_mul (x - 1) s
    have e : 1 + (x - 1) = x := by ring
    rw [e, hxt] at hC
    have hsu : IsUnit (s : O) := gradNPf_unit_nat v ι hinj hRR l hp.out hl s hs
    refine ⟨t * ((s : O) + (l : O) * (t * C)),
      ht.mul (lte_isUnit_add_mul_lemma_5 v ι hinj hRR _ _ _ hlO hsu), ?_⟩
    rw [← geom_sum_mul, hC, hxt]
    ring
  obtain ⟨ε0, hε0, he0⟩ := lte_pow_coprime_step_lemma_6 v ι hι hR l hl x t ht hxt s hsl
  have key : ∀ n : ℕ, ∃ E : O, IsUnit E ∧ ∏ y ∈ Ico 1 (n + 1), ((x ^ s) ^ y - 1) =
      (l : O) ^ (∑ y ∈ Ico 1 (n + 1), (1 + padicValNat l y)) * E := by
    intro n
    induction n with
    | zero => exact ⟨1, isUnit_one, by simp⟩
    | succ n ih =>
      obtain ⟨E, hE, hEq⟩ := ih
      obtain ⟨ε, hε, he⟩ := gradNPf_lte v ι hι hR l hl2 hl (x ^ s) ε0 hε0 he0
        (n + 1) (Nat.succ_ne_zero n)
      refine ⟨E * ε, hE.mul hε, ?_⟩
      rw [prod_Ico_succ_top (by omega : 1 ≤ n + 1), sum_Ico_succ_top (by omega : 1 ≤ n + 1),
        hEq, he]
      ring
  obtain ⟨E, hE, hEq⟩ := key N
  obtain ⟨u, rfl⟩ := hE
  refine ⟨↑u⁻¹, ?_⟩
  rw [hEq, gradNPf_sum_val l N]
  linear_combination (-((l : O) ^ (N + padicValNat l N.factorial))) * Units.inv_mul u

end GradNPfVal

end Formalism.MainNotions.N.Ln34
