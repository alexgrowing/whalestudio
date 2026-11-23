import Formalism.LocalToGlobal.CharacterGerms.SelfConjugateRowData

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.GmExArith

open Formalism.L2.FormalSeriesBounds NumberField

variable {C : Type} [Field C] {V : VF C}

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) :=
  lt_of_lt_of_le (lt_min ha hb) (V.v.map_add a b)

theorem mm_zero : V.MM (0 : C) := by
  unfold VF.MM; rw [V.v.map_zero]; exact WithTop.top_pos

theorem mm_neg {a : C} (h : V.MM a) : V.MM (-a) := by
  unfold VF.MM at *; rwa [V.v.map_neg]

theorem mm_sub {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a - b) := by
  rw [sub_eq_add_neg]; exact mm_add ha (mm_neg hb)

theorem mm_ge {a : C} (h : V.MM a) : V.Ge 0 a := by
  unfold VF.Ge; rw [WithTop.coe_zero]; exact le_of_lt h

theorem mm_mul_int {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  unfold VF.MM at *
  rw [V.v.map_mul]
  have hb' : (0 : WithTop ℝ) ≤ V.v b := by simpa [VF.Ge] using hb
  exact add_pos_of_pos_of_nonneg ha hb'

theorem mm_int_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  rw [mul_comm]; exact mm_mul_int hb ha

theorem mm_l : V.MM (V.l : C) := by
  unfold VF.MM; rw [V.v_l]; exact zero_lt_one

theorem not_mm_one : ¬ V.MM (1 : C) := by
  unfold VF.MM; rw [V.v.map_one]; exact lt_irrefl 0

theorem mm_of_ge {ε : ℝ} (hε : 0 < ε) {a : C} (h : V.Ge ε a) : V.MM a :=
  lt_of_lt_of_le (by exact_mod_cast hε) h

theorem mm_pow {a : C} (h : V.MM a) {n : ℕ} (hn : n ≠ 0) : V.MM (a ^ n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pow_succ]; exact mm_int_mul ((mm_ge h).pow k) h

theorem mm_sum {ι : Type*} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact mm_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact mm_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem v_eq_zero_of {a : C} (h0 : V.Ge 0 a) (h : ¬ V.MM a) : V.v a = 0 :=
  le_antisymm (not_lt.1 h) (by simpa [VF.Ge] using h0)

theorem ge_pow' {r : ℝ} {a : C} (h : V.Ge r a) (k : ℕ) : V.Ge ((k : ℝ) * r) (a ^ k) := by
  induction k with
  | zero => rw [Nat.cast_zero, zero_mul, pow_zero]; exact VF.Ge.one
  | succ k ih =>
    rw [pow_succ]
    have := ih.mul h
    convert this using 1
    push_cast; ring

theorem ge_natCast' (n : ℕ) : V.Ge 0 (n : C) := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact VF.Ge.zero 0
  | succ n ih => rw [Nat.cast_succ]; exact ih.add VF.Ge.one

theorem ge_intCast' (m : ℤ) : V.Ge 0 (m : C) := by
  cases m with
  | ofNat n => rw [Int.ofNat_eq_natCast, Int.cast_natCast]; exact ge_natCast' n
  | negSucc n => rw [Int.cast_negSucc]; exact (ge_natCast' (n + 1)).neg

theorem eq_zero_of_ge_all {x : C} (h : ∀ n : ℕ, V.Ge n x) : x = 0 := by
  by_contra hx
  have ht : V.v x ≠ ⊤ := by rwa [Ne, AddValuation.top_iff]
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 ht
  obtain ⟨n, hn⟩ := exists_nat_gt r
  have h1 := h n
  unfold VF.Ge at h1
  rw [← hr] at h1
  exact absurd (WithTop.coe_le_coe.1 h1) (not_le.2 hn)

theorem ge_of_isIntegral {z : C} (hz : IsIntegral ℤ z) : V.Ge 0 z := by
  by_contra hneg
  obtain ⟨p, hpm, hp⟩ := hz
  have hz0 : z ≠ 0 := by rintro rfl; exact hneg (VF.Ge.zero 0)
  have hw : V.MM z⁻¹ := by
    unfold VF.Ge at hneg; unfold VF.MM
    have e : V.v z + V.v z⁻¹ = 0 := by rw [← V.v.map_mul, mul_inv_cancel₀ hz0, V.v.map_one]
    induction ha : V.v z using WithTop.recTopCoe with
    | top => rw [ha] at hneg; exact absurd le_top hneg
    | coe r =>
      rw [ha] at hneg e
      have hr : r < 0 := by
        by_contra hr; exact hneg (by exact_mod_cast not_lt.1 hr)
      induction hb : V.v z⁻¹ using WithTop.recTopCoe with
      | top => exact WithTop.top_pos
      | coe s =>
        rw [hb] at e
        have e2 : r + s = 0 := by exact_mod_cast e
        exact_mod_cast (show (0 : ℝ) < s by linarith)
  have h0 : Polynomial.aeval z p = 0 := by rw [Polynomial.aeval_def]; exact hp
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, one_smul] at h0
  have hn : ∀ i ∈ Finset.range p.natDegree, V.MM ((p.coeff i • z ^ i) * z⁻¹ ^ p.natDegree) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have e : (p.coeff i • z ^ i) * z⁻¹ ^ p.natDegree = (p.coeff i : C) * z⁻¹ ^ (p.natDegree - i) := by
      rw [pow_sub₀ _ (inv_ne_zero hz0) hi'.le, ← inv_pow, inv_inv, zsmul_eq_mul]; ring
    rw [e]
    exact mm_int_mul (ge_intCast' _) (mm_pow hw (by omega))
  have e : (∑ i ∈ Finset.range p.natDegree, p.coeff i • z ^ i + z ^ p.natDegree) * z⁻¹ ^ p.natDegree
      = 0 * z⁻¹ ^ p.natDegree := by rw [h0]
  rw [add_mul, zero_mul, Finset.sum_mul, ← mul_pow, mul_inv_cancel₀ hz0, one_pow] at e
  have h1 : (1 : C) = -∑ i ∈ Finset.range p.natDegree, (p.coeff i • z ^ i) * z⁻¹ ^ p.natDegree := by
    linear_combination e
  have := mm_neg (mm_sum hn)
  rw [← h1] at this
  exact not_mm_one this

theorem ge_inv_two [CharZero C] (hl2 : V.l ≠ 2) : V.Ge 0 ((2 : C)⁻¹) := by
  have hcop : IsCoprime ((2 : ℕ) : ℤ) ((V.l : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes Nat.prime_two V.l_prime).2 (Ne.symm hl2))
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (a : C) * 2 + (b : C) * (V.l : C) = 1 := by
    have := congrArg (Int.cast : ℤ → C) hab
    push_cast at this
    exact this
  have hn2 : ¬ V.MM (2 : C) := by
    intro h
    apply not_mm_one (V := V)
    rw [← h1]
    exact mm_add (mm_int_mul (ge_intCast' a) h) (mm_int_mul (ge_intCast' b) mm_l)
  have h2int : V.Ge 0 (2 : C) := by
    have := (VF.Ge.one (V := V)).add (VF.Ge.one (V := V)); rwa [one_add_one_eq_two] at this
  have hv2 : V.v (2 : C) = 0 := v_eq_zero_of h2int hn2
  have e : V.v (2 : C) + V.v (2 : C)⁻¹ = 0 := by
    rw [← V.v.map_mul, mul_inv_cancel₀ two_ne_zero, V.v.map_one]
  rw [hv2, zero_add] at e
  unfold VF.Ge; rw [e]; simp

theorem geom_int {A B : C} (hA : V.Ge 0 A) (hB : V.Ge 0 B) (n : ℕ) :
    V.Ge 0 (∑ i ∈ Finset.range n, A ^ i * B ^ (n - 1 - i)) :=
  VF.Ge.sum fun i _ => (hA.pow i).mul_int (hB.pow _)

theorem ge_pow_sub {A B : C} (hA : V.Ge 0 A) (hB : V.Ge 0 B) {w : ℝ} (h : V.Ge w (A - B)) (n : ℕ) :
    V.Ge w (A ^ n - B ^ n) := by
  rw [← geom_sum₂_mul]; exact (geom_int hA hB n).mul_int h

theorem mm_pow_sub {A B : C} (hA : V.Ge 0 A) (hB : V.Ge 0 B) (h : V.MM (A - B)) (n : ℕ) :
    V.MM (A ^ n - B ^ n) := by
  rw [← geom_sum₂_mul]; exact mm_int_mul (geom_int hA hB n) h

theorem ge_pow_l_sub {A B : C} (hA : V.Ge 0 A) (hB : V.Ge 0 B) {w ε : ℝ} (h : V.Ge w (A - B))
    (hε : ε ≤ 1) (hεw : ε ≤ w) : V.Ge (w + ε) (A ^ V.l - B ^ V.l) := by
  rw [← geom_sum₂_mul, show w + ε = ε + w from add_comm w ε]
  refine VF.Ge.mul ?_ h
  have e2 : ∀ i ∈ Finset.range V.l, B ^ i * B ^ (V.l - 1 - i) = B ^ (V.l - 1) := by
    intro i hi
    rw [← pow_add]; congr 1
    have := Finset.mem_range.1 hi; omega
  have e : ∑ i ∈ Finset.range V.l, A ^ i * B ^ (V.l - 1 - i) =
      ∑ i ∈ Finset.range V.l, (A ^ i - B ^ i) * B ^ (V.l - 1 - i) + (V.l : C) * B ^ (V.l - 1) := by
    rw [show (V.l : C) * B ^ (V.l - 1) = ∑ i ∈ Finset.range V.l, B ^ i * B ^ (V.l - 1 - i) by
      rw [Finset.sum_congr rfl e2, Finset.sum_const, Finset.card_range, nsmul_eq_mul]]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  refine VF.Ge.add (VF.Ge.sum fun i _ => ?_) ?_
  · rw [mul_comm]; exact (hB.pow _).mul_int ((ge_pow_sub hA hB h i).mono hεw)
  · rw [mul_comm]; exact (hB.pow _).mul_int ((VF.ge_l (V := V)).mono hε)

theorem ge_pow_lpow_sub {A B : C} (hA : V.Ge 0 A) (hB : V.Ge 0 B) {w ε : ℝ} (h : V.Ge w (A - B))
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hεw : ε ≤ w) (k : ℕ) :
    V.Ge (w + k * ε) (A ^ (V.l ^ k) - B ^ (V.l ^ k)) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [pow_succ, pow_mul, pow_mul]
    have hk : ε ≤ w + k * ε := by
      have : (0 : ℝ) ≤ k * ε := mul_nonneg (Nat.cast_nonneg k) hε0
      linarith
    have h2 := ge_pow_l_sub (hA.pow _) (hB.pow _) ih hε hk
    convert h2 using 1
    push_cast; ring

theorem tele (z : ℕ → C) {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ k : ℕ, V.Ge ((k + 1 : ℝ) * ε) (z (k + 1) - z k))
    (k j : ℕ) (hkj : k ≤ j) : V.Ge ((k + 1 : ℝ) * ε) (z j - z k) := by
  induction j, hkj using Nat.le_induction with
  | base => rw [sub_self]; exact VF.Ge.zero _
  | succ j hkj ih =>
    have e : z (j + 1) - z k = (z (j + 1) - z j) + (z j - z k) := by ring
    rw [e]
    refine VF.Ge.add ((h j).mono ?_) ih
    have : (k : ℝ) ≤ j := by exact_mod_cast hkj
    exact mul_le_mul_of_nonneg_right (by linarith) hε

def Kf (ε : ℝ) (n : ℕ) : ℕ := ⌈(n : ℝ) / ε⌉₊

theorem Kf_spec {ε : ℝ} (hε : 0 < ε) (n : ℕ) : (n : ℝ) ≤ (Kf ε n : ℝ) * ε := by
  have := Nat.le_ceil ((n : ℝ) / ε)
  unfold Kf
  rwa [div_le_iff₀ hε] at this

theorem Kf_mono {ε : ℝ} (hε : 0 < ε) {n m : ℕ} (h : n ≤ m) : Kf ε n ≤ Kf ε m := by
  unfold Kf
  exact Nat.ceil_mono (div_le_div_of_nonneg_right (by exact_mod_cast h) hε.le)

def Cpl (V : VF C) : Prop :=
  ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)

theorem lim_of (z : ℕ → C) {ε : ℝ} (hC : Cpl V) (hε : 0 < ε)
    (h : ∀ k : ℕ, V.Ge ((k + 1 : ℝ) * ε) (z (k + 1) - z k)) :
    ∃ t, ∀ n : ℕ, V.Ge n (t - z (Kf ε n)) := by
  refine hC (fun n => z (Kf ε n)) fun n => ?_
  refine (tele z hε.le h _ _ (Kf_mono hε (Nat.le_succ n))).mono ?_
  have := Kf_spec hε n
  rw [add_mul, one_mul]
  linarith

theorem eps_of_mm {ι : Type} [Finite ι] (f : ι → C) (h : ∀ i, V.MM (f i)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ i, V.Ge ε (f i) := by
  have h1 : ∀ i, ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ V.Ge e (f i) := by
    intro i
    have hi := h i
    unfold VF.MM at hi
    induction hv : V.v (f i) using WithTop.recTopCoe with
    | top => exact ⟨1, one_pos, le_rfl, by unfold VF.Ge; rw [hv]; exact le_top⟩
    | coe r =>
      rw [hv] at hi
      have hr : 0 < r := by exact_mod_cast hi
      exact ⟨min r 1, lt_min hr one_pos, min_le_right _ _, by
        unfold VF.Ge; rw [hv]; exact_mod_cast min_le_left r 1⟩
  choose e he0 he1 heg using h1
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, le_rfl, fun i => (IsEmpty.false i).elim⟩
  · obtain ⟨i0, hi0⟩ := Finite.exists_min e
    exact ⟨e i0, he0 i0, he1 i0, fun i => (heg i).mono (hi0 i)⟩

theorem eq_one_of {u : C} {N : ℕ} (hN : V.MM ((N : C) + 1)) (hu1 : u ^ N = 1) (hum : V.MM (u - 1)) : u = 1 := by
  have hui : V.Ge 0 u := by
    have : u = (u - 1) + 1 := by ring
    rw [this]; exact (mm_ge hum).add VF.Ge.one
  have hS : V.MM ((∑ i ∈ Finset.range N, u ^ i) + 1) := by
    have e : (∑ i ∈ Finset.range N, u ^ i) + 1 =
        (∑ i ∈ Finset.range N, (u ^ i - 1 ^ i)) + ((N : C) + 1) := by
      rw [Finset.sum_sub_distrib]
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      ring
    rw [e]
    exact mm_add (mm_sum fun i _ => mm_pow_sub hui VF.Ge.one hum i) hN
  have hS0 : (∑ i ∈ Finset.range N, u ^ i) ≠ 0 := by
    intro h0; rw [h0, zero_add] at hS; exact not_mm_one hS
  have h3 : (∑ i ∈ Finset.range N, u ^ i) * (u - 1) = 0 := by
    rw [geom_sum_mul, hu1, sub_self]
  exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left hS0)

theorem frob_iter {R : Type} [CommRing R] {d : ℕ} (ψ : ZMod d → R →+* C) (hint : ∀ a x, V.Ge 0 (ψ a x))
    (frob : ∀ a x, V.MM (ψ (a + 1) x - ψ a x ^ V.l)) (x : R) (j : ℕ) :
    V.MM (ψ (j : ZMod d) x - ψ 0 x ^ (V.l ^ j)) := by
  induction j with
  | zero => rw [Nat.cast_zero, pow_zero, pow_one, sub_self]; exact mm_zero
  | succ j ih =>
    have e : ψ ((j + 1 : ℕ) : ZMod d) x - ψ 0 x ^ (V.l ^ (j + 1)) =
        (ψ ((j : ZMod d) + 1) x - ψ (j : ZMod d) x ^ V.l) +
          (ψ (j : ZMod d) x ^ V.l - (ψ 0 x ^ (V.l ^ j)) ^ V.l) := by
      rw [Nat.cast_succ, ← pow_mul, ← pow_succ]; ring
    rw [e]
    exact mm_add (frob _ x) (mm_pow_sub (hint _ x) ((hint 0 x).pow _) ih V.l)

theorem resid {R : Type} [CommRing R] {d : ℕ} [NeZero d] (ψ : ZMod d → R →+* C)
    (hint : ∀ a x, V.Ge 0 (ψ a x)) (frob : ∀ a x, V.MM (ψ (a + 1) x - ψ a x ^ V.l))
    (sep : ∀ a : ZMod d, a ≠ 0 → ∃ x, ¬ V.MM (ψ a x - ψ 0 x)) (hl2 : V.l ≠ 2) :
    ∃ x : R, V.MM (ψ 0 x ^ ((V.l ^ d - 1) / 2) + 1) := by
  have hl := V.l_prime
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hl3 : 3 ≤ V.l := by have := hl.two_le; omega
  have hQ3 : 3 ≤ V.l ^ d := le_trans hl3 (Nat.le_self_pow (Nat.pos_iff_ne_zero.1 hdpos) V.l)
  have hQodd : Odd (V.l ^ d) := (hl.eq_two_or_odd'.resolve_left hl2).pow
  have hQmod : V.l ^ d % 2 = 1 := Nat.odd_iff.1 hQodd
  let P : Ideal R :=
    { carrier := {x | V.MM (ψ 0 x)}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add] at *; exact mm_add ha hb
      zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]; exact mm_zero
      smul_mem' := fun c x hx => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at *; exact mm_int_mul (hint 0 c) hx }
  have hmem : ∀ x, x ∈ P ↔ V.MM (ψ 0 x) := fun x => Iff.rfl
  have hP : P.IsPrime := by
    refine ⟨?_, fun {x y} hxy => ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one, hmem, map_one]; exact not_mm_one
    · rw [hmem, map_mul] at hxy
      rw [hmem, hmem]
      by_contra hc
      push_neg at hc
      unfold VF.MM at hxy
      rw [V.v.map_mul, v_eq_zero_of (hint 0 x) hc.1, v_eq_zero_of (hint 0 y) hc.2, add_zero] at hxy
      exact lt_irrefl _ hxy
  have := hP
  have hfrobk : ∀ z : R ⧸ P, z ^ (V.l ^ d) = z := by
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [← map_pow, Ideal.Quotient.eq, hmem, map_sub, map_pow]
    have h1 := frob_iter ψ hint frob x d
    rw [ZMod.natCast_self] at h1
    have e : ψ 0 x ^ (V.l ^ d) - ψ 0 x = -(ψ 0 x - ψ 0 x ^ (V.l ^ d)) := by ring
    rw [e]; exact mm_neg h1
  have hunit : ∀ z : R ⧸ P, z ≠ 0 → z ^ (V.l ^ d - 1) = 1 := by
    intro z hz
    have h1 := hfrobk z
    have e : z ^ (V.l ^ d) = z * z ^ (V.l ^ d - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [e] at h1
    exact mul_left_cancel₀ hz (h1.trans (mul_one z).symm)
  have hfin : Finite (R ⧸ P) := by
    have hsub : ∀ z : R ⧸ P, z ∈ insert (0 : R ⧸ P)
        (Polynomial.nthRoots (V.l ^ d - 1) (1 : R ⧸ P)).toFinset := by
      intro z
      by_cases hz : z = 0
      · rw [hz]; exact Finset.mem_insert_self _ _
      · refine Finset.mem_insert_of_mem ?_
        rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)]
        exact hunit z hz
    exact Set.finite_univ_iff.1 ((Finset.finite_toSet _).subset fun z _ => hsub z)
  have := hfin
  have hmax : P.IsMaximal := Ideal.Quotient.maximal_of_isField P (Finite.isDomain_to_isField _)
  letI : Field (R ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (R ⧸ P) := Fintype.ofFinite _
  haveI : CharP (R ⧸ P) V.l := (CharP.charP_iff_prime_eq_zero hl).2 (by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem, hmem, map_natCast]
    exact mm_l)
  obtain ⟨n, -, hcard⟩ := FiniteField.card (R ⧸ P) V.l
  have hdn : d ≤ (n : ℕ) := by
    by_contra hlt
    push_neg at hlt
    have hn0 : ((n : ℕ) : ZMod d) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have := Nat.le_of_dvd n.pos hdvd
      omega
    obtain ⟨x, hx⟩ := sep _ hn0
    apply hx
    have h1 := frob_iter ψ hint frob x n
    have h2 : V.MM (ψ 0 x ^ (V.l ^ (n : ℕ)) - ψ 0 x) := by
      have := FiniteField.pow_card (Ideal.Quotient.mk P x)
      rw [hcard, ← map_pow, Ideal.Quotient.eq, hmem, map_sub, map_pow] at this
      exact this
    have e : ψ ((n : ℕ) : ZMod d) x - ψ 0 x =
        (ψ ((n : ℕ) : ZMod d) x - ψ 0 x ^ (V.l ^ (n : ℕ))) + (ψ 0 x ^ (V.l ^ (n : ℕ)) - ψ 0 x) := by ring
    rw [e]; exact mm_add h1 h2
  have hpos : 0 < (V.l ^ d - 1) / 2 := by omega
  have hm : ∃ z : R ⧸ P, z ^ ((V.l ^ d - 1) / 2) = -1 := by
    by_contra hno
    push_neg at hno
    have hsq : ∀ z : R ⧸ P, z ≠ 0 → z ^ ((V.l ^ d - 1) / 2) = 1 := by
      intro z hz
      have h2 : (z ^ ((V.l ^ d - 1) / 2)) * (z ^ ((V.l ^ d - 1) / 2)) = 1 := by
        rw [← pow_add, ← hunit z hz]; congr 1; omega
      rcases mul_self_eq_one_iff.1 h2 with h | h
      · exact h
      · exact absurd h (hno z)
    have hsub : (Finset.univ : Finset (R ⧸ P)) ⊆
        insert 0 (Polynomial.nthRoots ((V.l ^ d - 1) / 2) (1 : R ⧸ P)).toFinset := by
      intro z _
      by_cases hz : z = 0
      · rw [hz]; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (by
          rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hpos]; exact hsq z hz)
    have hc1 := Finset.card_le_card hsub
    have hc2 := Finset.card_insert_le (0 : R ⧸ P)
      (Polynomial.nthRoots ((V.l ^ d - 1) / 2) (1 : R ⧸ P)).toFinset
    have hc3 := Multiset.toFinset_card_le (Polynomial.nthRoots ((V.l ^ d - 1) / 2) (1 : R ⧸ P))
    have hc4 := Polynomial.card_nthRoots ((V.l ^ d - 1) / 2) (1 : R ⧸ P)
    rw [Finset.card_univ, hcard] at hc1
    have hpow : V.l ^ d ≤ V.l ^ (n : ℕ) := Nat.pow_le_pow_right hl.pos hdn
    omega
  obtain ⟨z, hz⟩ := hm
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨x, ?_⟩
  have h1 : Ideal.Quotient.mk P (x ^ ((V.l ^ d - 1) / 2) + 1) = 0 := by
    rw [map_add, map_pow, hz, map_one, neg_add_cancel]
  have h2 := (hmem _).1 (Ideal.Quotient.eq_zero_iff_mem.1 h1)
  rwa [map_add, map_pow, map_one] at h2

end Formalism.L2.FormalSeriesBounds.GmExArith
