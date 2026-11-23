import Mathlib

namespace GlobalTheory.Harm

open Finset

open Finset in

theorem _root_.GlobalTheory.Harm.sum_filter_lt_eq_sum_range {m : ℕ} (f : Fin m → ℤ) (i : ℕ) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin m => (k : ℕ) < i), f k =
      ∑ j ∈ range i, if h : j < m then f ⟨j, h⟩ else 0 := by
  rw [Finset.sum_filter]
  have hfin := Fin.sum_univ_eq_sum_range
    (fun j => if j < i then (if h : j < m then f ⟨j, h⟩ else 0) else 0) m
  simp only [Fin.is_lt, ↓reduceDIte, Fin.eta] at hfin
  rw [hfin, ← Finset.sum_filter]
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact hj.2
  · intro j hj hj'
    simp only [Finset.mem_filter, Finset.mem_range, not_and] at hj hj'
    have hjm : ¬ j < m := fun hjm => hj' hjm hj
    simp [hjm]

open Finset in
private theorem sum_range_sub_mul_eq_abel_summation (D e : ℕ → ℤ) (n : ℕ) :
    ∑ i ∈ range n, (D (i + 1) - D i) * e i =
      D n * e n + ∑ i ∈ range n, D (i + 1) * (e i - e (i + 1)) - D 0 * e 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, sum_range_succ, ih]; ring

open Finset in

theorem _root_.GlobalTheory.Harm.casimir_value_strict {m : ℕ} (κ κ₀ : Fin m → ℤ) (h : Antitone κ)
    (h₀ : Antitone κ₀)
    (hle : ∀ i : ℕ, ∑ k ∈ Finset.univ.filter (fun k : Fin m => (k : ℕ) < i), κ k ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin m => (k : ℕ) < i), κ₀ k)
    (hsum : ∑ k, κ k = ∑ k, κ₀ k)
    (hC : ∑ i, κ₀ i * (κ₀ i + m - 1 - 2 * (i : ℕ)) ≤ ∑ i, κ i * (κ i + m - 1 - 2 * (i : ℕ))) : κ = κ₀ := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ → ℤ, d = fun j =>
      (if h : j < m then κ₀ ⟨j, h⟩ else 0) - (if h : j < m then κ ⟨j, h⟩ else 0) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℤ, e = fun j =>
      if h : j < m then κ₀ ⟨j, h⟩ + κ ⟨j, h⟩ + (m : ℤ) - 1 - 2 * (j : ℤ) else 0 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℤ, D = fun j => ∑ i ∈ range j, d i := ⟨_, rfl⟩
  have hDj : ∀ j, D j = ∑ k ∈ univ.filter (fun k : Fin m => (k : ℕ) < j), κ₀ k -
      ∑ k ∈ univ.filter (fun k : Fin m => (k : ℕ) < j), κ k := by
    intro j
    simp only [hD, hd, sum_sub_distrib, _root_.GlobalTheory.Harm.sum_filter_lt_eq_sum_range]
  have hD0 : ∀ j, 0 ≤ D j := fun j => by rw [hDj]; linarith [hle j]
  have hDm : D m = 0 := by rw [hDj]; simp [hsum]
  have hDzero : D 0 = 0 := by simp [hD]
  have hdD : ∀ j, d j = D (j + 1) - D j := by intro j; simp [hD, sum_range_succ]
  have hC' : ∑ i ∈ range m, (D (i + 1) - D i) * e i ≤ 0 := by
    have h1 : ∑ i ∈ range m, d i * e i =
        ∑ i : Fin m, (κ₀ i - κ i) * (κ₀ i + κ i + m - 1 - 2 * (i : ℕ)) := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => d i * e i) m]
      refine sum_congr rfl (fun i _ => ?_)
      simp [hd, he, i.isLt]
    have h2 : ∑ i : Fin m, (κ₀ i - κ i) * (κ₀ i + κ i + m - 1 - 2 * (i : ℕ)) =
        ∑ i, κ₀ i * (κ₀ i + m - 1 - 2 * (i : ℕ)) - ∑ i, κ i * (κ i + m - 1 - 2 * (i : ℕ)) := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl (fun i _ => ?_)
      ring
    simp_rw [← hdD]
    rw [h1, h2]
    linarith
  have key := sum_range_sub_mul_eq_abel_summation D e m
  rw [hDm, hDzero, zero_mul, zero_mul, zero_add, sub_zero] at key
  have he_gap : ∀ i, i + 1 < m → 2 ≤ e i - e (i + 1) := by
    intro i hi
    have h1 := h₀ (Fin.mk_le_mk.mpr (Nat.le_succ i) : (⟨i, by omega⟩ : Fin m) ≤ ⟨i + 1, hi⟩)
    have h2 := h (Fin.mk_le_mk.mpr (Nat.le_succ i) : (⟨i, by omega⟩ : Fin m) ≤ ⟨i + 1, hi⟩)
    simp only [he, hi, show i < m by omega, ↓reduceDIte]
    push_cast
    linarith
  have hterm : ∀ i ∈ range m, 0 ≤ D (i + 1) * (e i - e (i + 1)) := by
    intro i hi
    rw [mem_range] at hi
    rcases Nat.lt_or_ge (i + 1) m with h' | h'
    · exact mul_nonneg (hD0 _) (by linarith [he_gap i h'])
    · rw [show i + 1 = m by omega, hDm, zero_mul]
  have hsum0 : ∑ i ∈ range m, D (i + 1) * (e i - e (i + 1)) = 0 :=
    le_antisymm (by linarith) (sum_nonneg hterm)
  have hall := (sum_eq_zero_iff_of_nonneg hterm).mp hsum0
  have hDall : ∀ j, j ≤ m → D j = 0 := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact hDzero
    rcases Nat.lt_or_ge j m with hjm | hjm
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rcases mul_eq_zero.mp (hall i (mem_range.mpr (by omega))) with h0 | h0
      · exact h0
      · linarith [he_gap i hjm]
    · rw [show j = m by omega]
      exact hDm
  funext k
  have hk' := k.isLt
  have hk := hdD k
  rw [hDall ((k : ℕ) + 1) (by omega), hDall (k : ℕ) (by omega)] at hk
  simp [hd, k.isLt] at hk
  linarith

def mixedWeight (m : ℕ) {p q : ℕ} (a : Fin p → ℕ) (b : Fin q → ℕ) : Fin m → ℤ := fun k =>
  (if h : (k : ℕ) < p then (a ⟨k, h⟩ : ℤ) else 0) -
    (if h : m - 1 - (k : ℕ) < q then (b ⟨m - 1 - k, h⟩ : ℤ) else 0)

theorem mixedWeight_apply (m : ℕ) {p q : ℕ} (a : Fin p → ℕ) (b : Fin q → ℕ) (k : Fin m) :
    mixedWeight m a b k =
      (if h : (k : ℕ) < p then (a ⟨k, h⟩ : ℤ) else 0) -
        (if h : m - 1 - (k : ℕ) < q then (b ⟨m - 1 - k, h⟩ : ℤ) else 0) := rfl

open Finset in

theorem _root_.GlobalTheory.Harm.antitone_mixedWeight (m : ℕ) {p q : ℕ} {a : Fin p → ℕ} {b : Fin q → ℕ}
    (ha : Antitone a) (hb : Antitone b) : Antitone (_root_.GlobalTheory.Harm.mixedWeight m a b) := by
  intro k l hkl
  have hkl' : (k : ℕ) ≤ l := hkl
  simp only [_root_.GlobalTheory.Harm.mixedWeight_apply]
  have hA : (if h : (l : ℕ) < p then (a ⟨l, h⟩ : ℤ) else 0) ≤
      (if h : (k : ℕ) < p then (a ⟨k, h⟩ : ℤ) else 0) := by
    split_ifs <;> first
      | omega | positivity | exact le_rfl | exact_mod_cast ha (Fin.mk_le_mk.mpr hkl')
  have hB : (if h : m - 1 - (k : ℕ) < q then (b ⟨m - 1 - k, h⟩ : ℤ) else 0) ≤
      (if h : m - 1 - (l : ℕ) < q then (b ⟨m - 1 - l, h⟩ : ℤ) else 0) := by
    split_ifs <;> first
      | omega | positivity | exact le_rfl | exact_mod_cast hb (Fin.mk_le_mk.mpr (by omega))
  linarith

open Finset in

theorem _root_.GlobalTheory.Harm.sum_dite_lt {m p : ℕ} (hp : p ≤ m) (f : Fin p → ℤ) :
    ∑ k : Fin m, (if h : (k : ℕ) < p then f ⟨k, h⟩ else 0) = ∑ k, f k := by
  have hfin := Fin.sum_univ_eq_sum_range (fun j => if h : j < p then f ⟨j, h⟩ else 0) m
  have hfin' := Fin.sum_univ_eq_sum_range (fun j => if h : j < p then f ⟨j, h⟩ else 0) p
  beta_reduce at hfin
  simp only [Fin.is_lt, ↓reduceDIte, Fin.eta] at hfin'
  rw [hfin, hfin']
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  · intro j _ hj
    simp only [Finset.mem_range] at hj
    simp [hj]

open Finset in

theorem _root_.GlobalTheory.Harm.sum_dite_rev_lt {m q : ℕ} (hq : q ≤ m) (f : Fin q → ℤ) :
    ∑ k : Fin m, (if h : m - 1 - (k : ℕ) < q then f ⟨m - 1 - k, h⟩ else 0) = ∑ k, f k := by
  rw [← _root_.GlobalTheory.Harm.sum_dite_lt hq f]
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun k => ?_)
  have hk : ((Fin.revPerm k : Fin m) : ℕ) = m - 1 - k := by
    simp only [Fin.revPerm_apply, Fin.val_rev]
    omega
  simp only [hk]

open Finset in

theorem _root_.GlobalTheory.Harm.sum_mixedWeight {m p q : ℕ} (h : p + q ≤ m) (a : Fin p → ℕ) (b : Fin q → ℕ) :
    ∑ k, _root_.GlobalTheory.Harm.mixedWeight m a b k = ∑ i, (a i : ℤ) - ∑ i, (b i : ℤ) := by
  have h1 := _root_.GlobalTheory.Harm.sum_dite_lt (m := m) (by omega : p ≤ m)
    (fun i => (a i : ℤ))
  have h2 := _root_.GlobalTheory.Harm.sum_dite_rev_lt (m := m) (by omega : q ≤ m)
    (fun i => (b i : ℤ))
  beta_reduce at h1 h2
  simp only [_root_.GlobalTheory.Harm.mixedWeight_apply, Finset.sum_sub_distrib]
  rw [h1, h2]

open Finset in

theorem _root_.GlobalTheory.Harm.casimir_value_mixedWeight {m p q : ℕ} (h : p + q ≤ m) (a : Fin p → ℕ) (b : Fin q → ℕ) :
    ∑ k : Fin m, _root_.GlobalTheory.Harm.mixedWeight m a b k * (_root_.GlobalTheory.Harm.mixedWeight m a b k + m - 1 - 2 * (k : ℕ)) =
      (∑ i : Fin p, (a i : ℤ) * (a i + p - 1 - 2 * (i : ℕ)) + ((m : ℤ) - p) * ∑ i, (a i : ℤ)) +
      (∑ i : Fin q, (b i : ℤ) * (b i + q - 1 - 2 * (i : ℕ)) + ((m : ℤ) - q) * ∑ i, (b i : ℤ)) := by
  have hp : p ≤ m := by omega
  have hq : q ≤ m := by omega
  have h1 := _root_.GlobalTheory.Harm.sum_dite_lt hp
    (fun i : Fin p => (a i : ℤ) * (a i + m - 1 - 2 * (i : ℕ)))
  have h2 := _root_.GlobalTheory.Harm.sum_dite_rev_lt hq
    (fun j : Fin q => (b j : ℤ) * (b j + m - 1 - 2 * (j : ℕ)))
  beta_reduce at h1 h2
  simp only [Fin.val_mk] at h1 h2
  have hpt : ∀ k : Fin m, _root_.GlobalTheory.Harm.mixedWeight m a b k *
        (_root_.GlobalTheory.Harm.mixedWeight m a b k + m - 1 - 2 * (k : ℕ)) =
      (if h : (k : ℕ) < p then (a ⟨k, h⟩ : ℤ) * (a ⟨k, h⟩ + m - 1 - 2 * (k : ℕ)) else 0) +
      (if h : m - 1 - (k : ℕ) < q then
        (b ⟨m - 1 - k, h⟩ : ℤ) * (b ⟨m - 1 - k, h⟩ + m - 1 - 2 * (m - 1 - (k : ℕ) : ℕ))
        else 0) := by
    intro k
    have hk := k.isLt
    have hc : ((m - 1 - (k : ℕ) : ℕ) : ℤ) = (m : ℤ) - 1 - (k : ℕ) := by omega
    rw [_root_.GlobalTheory.Harm.mixedWeight_apply]
    split_ifs <;> first | omega | (rw [hc]; ring) | ring
  rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_add_distrib, h1, h2,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1 <;> refine Finset.sum_congr rfl (fun i _ => ?_) <;> ring

end GlobalTheory.Harm
