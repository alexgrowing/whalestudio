import Mathlib

namespace UpperTheory

variable {E K K' : Type} [Field E] [Field K] [Field K'] {ι ι' : Type} [Fintype ι] [Fintype ι']

def MU (φ : ι → E →+* K) (e : ι → ℤ) : Prop :=
  ∀ z : E, (∃ m : ℕ, 0 < m ∧ z ^ m = 1) → ∏ i, φ i z ^ e i = 1

def MUQ (φ : ι → E →+* K) (e : ι → ℚ) : Prop :=
  ∃ a : ι → ℤ, (∀ i, e i = a i) ∧ MU φ a

theorem root_ne_zero {z : E} (hz : ∃ m : ℕ, 0 < m ∧ z ^ m = 1) : z ≠ 0 := by
  obtain ⟨m, hm, h⟩ := hz
  rintro rfl
  rw [zero_pow hm.ne'] at h
  exact zero_ne_one h

theorem prod_neg_one_zpow (e : ι → ℤ) : ∏ i, (-1 : K) ^ e i = (-1) ^ (∑ i, e i) := by
  classical
  refine Finset.induction_on (motive := fun s => ∏ i ∈ s, (-1 : K) ^ e i = (-1) ^ (∑ i ∈ s, e i)) Finset.univ (by simp) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ (by norm_num)]

namespace MU

variable {φ : ι → E →+* K} {e e' : ι → ℤ}

theorem zero : MU φ 0 := fun _ _ => by simp

theorem add (h : MU φ e) (h' : MU φ e') : MU φ (e + e') := by
  intro z hz
  have hne : ∀ i, φ i z ≠ 0 := fun i => (map_ne_zero (φ i)).2 (root_ne_zero hz)
  show ∏ i, φ i z ^ (e i + e' i) = 1
  rw [Finset.prod_congr rfl fun i _ => zpow_add₀ (hne i) (e i) (e' i), Finset.prod_mul_distrib, h z hz, h' z hz, one_mul]

theorem neg (h : MU φ e) : MU φ (-e) := by
  intro z hz
  show ∏ i, φ i z ^ (-e i) = 1
  simp_rw [zpow_neg]
  rw [Finset.prod_inv_distrib, h z hz, inv_one]

theorem smul (h : MU φ e) (c : ℤ) : MU φ (fun i => c * e i) := by
  intro z hz
  show ∏ i, φ i z ^ (c * e i) = 1
  simp_rw [mul_comm c, zpow_mul]
  rw [Finset.prod_zpow, h z hz, one_zpow]

theorem const (h : MU φ (fun _ => 1)) (c : ℤ) : MU φ (fun _ => c) := by
  have h2 := h.smul c
  simpa using h2

theorem add_const (h : MU φ e) (h1 : MU φ (fun _ => 1)) (c : ℤ) : MU φ (fun i => e i + c) :=
  h.add (h1.const c)

theorem equiv_iff (s : ι' ≃ ι) : MU (fun i => φ (s i)) (fun i => e (s i)) ↔ MU φ e := by
  refine forall_congr' fun z => forall_congr' fun _ => ?_
  rw [Equiv.prod_comp s (fun i => φ i z ^ e i)]

theorem aut (h : MU φ e) (g : E →+* E) : MU (fun i => (φ i).comp g) e := fun z hz => by
  obtain ⟨m, hm, hzm⟩ := hz
  exact h (g z) ⟨m, hm, by rw [← map_pow, hzm, map_one]⟩

theorem even [CharZero K] (h : MU φ e) : Even (∑ i, e i) := by
  have h1 := h (-1) ⟨2, by norm_num, by norm_num⟩
  simp only [map_neg, map_one] at h1
  rw [prod_neg_one_zpow] at h1
  by_contra hodd
  rw [Int.not_even_iff_odd] at hodd
  rw [hodd.neg_one_zpow] at h1
  norm_num at h1

end MU

namespace MUQ

variable {φ : ι → E →+* K} {e : ι → ℚ}

theorem int (h : MUQ φ e) (i : ι) : ∃ z : ℤ, e i = z := let ⟨a, ha, _⟩ := h; ⟨a i, ha i⟩

theorem even [CharZero K] (h : MUQ φ e) : ∃ z : ℤ, ∑ i, e i = 2 * (z : ℚ) := by
  obtain ⟨a, ha, hm⟩ := h
  obtain ⟨z, hz⟩ := hm.even
  refine ⟨z, ?_⟩
  simp only [ha]
  rw [← Int.cast_sum, hz]
  push_cast
  ring

theorem mu (h : MUQ φ e) {a : ι → ℤ} (ha : ∀ i, e i = a i) : MU φ a := by
  obtain ⟨b, hb, hm⟩ := h
  have hab : a = b := funext fun i => by
    have h3 := (ha i).symm.trans (hb i)
    exact_mod_cast h3
  subst hab
  exact hm

theorem equiv_iff (s : ι' ≃ ι) : MUQ (fun i => φ (s i)) (fun i => e (s i)) ↔ MUQ φ e := by
  constructor
  · rintro ⟨a, ha, hm⟩
    refine ⟨fun i => a (s.symm i), fun i => by simpa using ha (s.symm i), ?_⟩
    rw [← MU.equiv_iff s]
    simpa using hm
  · rintro ⟨a, ha, hm⟩
    exact ⟨fun i => a (s i), fun i => ha _, (MU.equiv_iff s).2 hm⟩

theorem add_const (h : MUQ φ e) (h1 : MU φ (fun _ => 1)) (c : ℤ) : MUQ φ (fun i => e i + c) := by
  obtain ⟨a, ha, hm⟩ := h
  exact ⟨fun i => a i + c, fun i => by simp [ha], hm.add_const h1 c⟩

end MUQ

end UpperTheory
