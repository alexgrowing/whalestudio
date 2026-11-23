import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.NegDminusLeMu

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {N r K : ℕ}

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

theorem two_N_lt_K (H : HypT N n0 r K LL B od bb a La p) : 2 * N < K := by
  have h := H.H4
  have hr := H.r1
  have hk : (0 : ℝ) < ((r + K : ℕ) : ℝ) := by
    have : 0 < r + K := by omega
    exact_mod_cast this
  have : (2 * N : ℝ) < (K : ℝ) := by linarith
  exact_mod_cast this

theorem dplus_le_beA (_H : HypT N n0 r K LL B od bb a La p) {dd : Fin N → ℕ}
    (hdd : ∀ i : Fin N, i.val < n0 → dd i = B i) (s : ℕ) (hs : s ≤ n0) : dplus LL dd s ≤ beA n0 B := by
  unfold dplus beA
  refine Finset.sum_le_sum fun l _ => ?_
  by_cases hl : l.val < s ∧ LL.vec l = true
  · rw [if_pos hl, if_pos (by omega), hdd l (by omega)]
  · rw [if_neg hl]; exact Nat.zero_le _

theorem dminus_le_beA (H : HypT N n0 r K LL B od bb a La p) {dd : Fin N → ℕ}
    (hdd : ∀ i : Fin N, i.val < n0 → dd i = B i) (s : ℕ) : dminus LL dd s ≤ beA n0 B := by
  unfold dminus beA
  refine Finset.sum_le_sum fun l _ => ?_
  by_cases hl : l.val < s ∧ LL.vec l = false
  · have hln : l.val < n0 := by
      by_contra hcon
      have := H.vec_true_of_late l (by omega)
      rw [hl.2] at this
      exact absurd this (by simp)
    rw [if_pos hl, if_pos hln, hdd l hln]
  · rw [if_neg hl]; exact Nat.zero_le _

theorem path_le_beA (H : HypT N n0 r K LL B od bb a La p) {dd : Fin N → ℕ} (P : PPath (r + K) N LL dd)
    (hP : IsPATHa LL n0 B P.mu dd) :
    ∀ (s : ℕ) (hs : s < N + 1) (m : Fin (r + K)), P.mu ⟨s, hs⟩ m ≤ (beA n0 B : ℤ) := by
  intro s
  induction s with
  | zero =>
    intro hs m
    have h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0 := rfl
    rw [h0, P.zero]; simp
  | succ s ih =>
    intro hs m
    by_cases hsn : s + 1 ≤ n0
    · refine le_trans (mu_le_dplus P (s + 1) hs m) ?_
      exact_mod_cast dplus_le_beA H hP.degs (s + 1) hsn
    · have hsN : s < N := by omega
      have hv : LL.vec ⟨s, hsN⟩ = true := H.vec_true_of_late ⟨s, hsN⟩ (by simp only; omega)
      by_cases hm : m.val = 0
      · have := hP.head ⟨s, hsN⟩ m (by simp only; omega) (by omega)
        exact le_of_eq this
      · have h := step_vec P ⟨s, hsN⟩ hv
        have hm1 : (m.val - 1) + 1 < r + K := by have := m.2; omega
        have h2 := h.2.1 ⟨m.val - 1, by have := m.2; omega⟩ hm1
        have hme : (⟨(m.val - 1) + 1, hm1⟩ : Fin (r + K)) = m := Fin.ext (by simp only; omega)
        rw [hme] at h2
        exact le_trans h2 (ih (by omega) _)

theorem beA_le (H : HypT N n0 r K LL B od bb a La p) : (beA n0 B : ℝ) ≤ 2 * a * (N : ℝ) := by
  unfold beA
  push_cast
  have ha : (0 : ℝ) ≤ 2 * a := by have := H.a3; linarith
  calc ∑ i : Fin N, (if i.val < n0 then (B i : ℝ) else 0) ≤ ∑ _i : Fin N, 2 * a := by
        refine Finset.sum_le_sum fun i _ => ?_
        by_cases hi : i.val < n0
        · rw [if_pos hi]; exact (H.H1 i hi).2
        · rw [if_neg hi]; exact ha
    _ = 2 * a * (N : ℝ) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end

def code (N r K : ℕ) (μ : Fin (N + 1) → Fin (r + K) → ℤ) : Fin N × Fin (2 * N) → ℕ := fun v =>
  if h : v.2.val < N ∧ v.2.val < r + K then (μ v.1.succ ⟨v.2.val, h.2⟩).toNat
  else if h' : r + K - 2 * N + v.2.val < r + K then (-μ v.1.succ ⟨r + K - 2 * N + v.2.val, h'⟩).toNat else 0

theorem path_count_finite : PathCountFinite := by
  classical
  intro N n0 r K _ _ LL B od bb a La p H
  have hK := two_N_lt_K H
  set M := beA n0 B with hM
  let t : Finset (Fin N × Fin (2 * N) → ℕ) := Fintype.piFinset fun _ => Finset.range (M + 1)
  have hshape : ∀ μ ∈ SP (r := r) (K := K) LL n0 B, ∀ (s : Fin (N + 1)) (m : Fin (r + K)),
      (m.val + N < r + K → 0 ≤ μ s m) ∧ (N ≤ m.val → μ s m ≤ 0) ∧ μ s m ≤ (M : ℤ) ∧ -(M : ℤ) ≤ μ s m := by
    rintro μ ⟨dd, hP⟩ s m
    obtain ⟨P, rfl⟩ := hP.path
    refine ⟨fun h => mu_nonneg P s.val s.2 m (by have := s.2; omega),
      fun h => mu_nonpos P s.val s.2 m (by have := s.2; omega), path_le_beA H P hP s.val s.2 m, ?_⟩
    refine le_trans ?_ (neg_dminus_le_mu P s.val s.2 m)
    have := dminus_le_beA H hP.degs s.val
    have h' : (dminus LL dd s.val : ℤ) ≤ (M : ℤ) := by exact_mod_cast this
    linarith
  have hmaps : ∀ μ ∈ SP (r := r) (K := K) LL n0 B, code N r K μ ∈ (t : Set (Fin N × Fin (2 * N) → ℕ)) := by
    intro μ hμ
    simp only [t, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range]
    intro v
    unfold code
    split_ifs with h h'
    · have := (hshape μ hμ v.1.succ ⟨v.2.val, h.2⟩).2.2.1
      omega
    · have := (hshape μ hμ v.1.succ ⟨r + K - 2 * N + v.2.val, h'⟩).2.2.2
      omega
    · omega
  have hinj : Set.InjOn (code N r K) (SP (r := r) (K := K) LL n0 B) := by
    intro μ hμ μ' hμ' hc
    funext s m
    induction s using Fin.cases with
    | zero =>
      obtain ⟨dd, hP⟩ := hμ
      obtain ⟨dd', hP'⟩ := hμ'
      obtain ⟨P, rfl⟩ := hP.path
      obtain ⟨P', rfl⟩ := hP'.path
      rw [P.zero, P'.zero]
    | succ i =>
      have h1 := hshape μ hμ i.succ m
      have h2 := hshape μ' hμ' i.succ m
      by_cases hm : m.val < N
      · have hcv := congrFun hc (i, ⟨m.val, by omega⟩)
        unfold code at hcv
        rw [dif_pos ⟨hm, m.2⟩, dif_pos ⟨hm, m.2⟩] at hcv
        have e1 := h1.1 (by omega)
        have e2 := h2.1 (by omega)
        have hcv' : (μ i.succ m).toNat = (μ' i.succ m).toNat := hcv
        omega
      · by_cases hm2 : m.val + N < r + K
        · have e1 := h1.1 hm2
          have e2 := h2.1 hm2
          have e3 := h1.2.1 (by omega)
          have e4 := h2.2.1 (by omega)
          omega
        · have hidx : m.val - (r + K - 2 * N) < 2 * N := by have := m.2; omega
          have hcv := congrFun hc (i, ⟨m.val - (r + K - 2 * N), hidx⟩)
          unfold code at hcv
          have hn1 : ¬ ((m.val - (r + K - 2 * N)) < N ∧ (m.val - (r + K - 2 * N)) < r + K) := by omega
          have hn2 : r + K - 2 * N + (m.val - (r + K - 2 * N)) < r + K := by have := m.2; omega
          rw [dif_neg hn1, dif_neg hn1, dif_pos hn2, dif_pos hn2] at hcv
          have hme : (⟨r + K - 2 * N + (m.val - (r + K - 2 * N)), hn2⟩ : Fin (r + K)) = m :=
            Fin.ext (by simp only; omega)
          rw [hme] at hcv
          have hcv' : (-μ i.succ m).toNat = (-μ' i.succ m).toNat := hcv
          have e3 := h1.2.1 (by omega)
          have e4 := h2.2.1 (by omega)
          omega
  have hfin : (SP (r := r) (K := K) LL n0 B).Finite :=
    Set.Finite.of_injOn (fun μ hμ => hmaps μ hμ) hinj t.finite_toSet
  refine ⟨hfin, ?_⟩
  have hle := Set.ncard_le_ncard_of_injOn (code N r K) hmaps hinj t.finite_toSet
  rw [Set.ncard_coe_finset] at hle
  have hcard : t.card = (M + 1) ^ (N * (2 * N)) := by
    simp [t, Fintype.card_piFinset]
  rw [hcard] at hle
  have hA : (0 : ℝ) < 1 + 2 * a * (N : ℝ) := by
    have := H.a3
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hM1 : ((M + 1 : ℕ) : ℝ) ≤ 1 + 2 * a * (N : ℝ) := by
    have := beA_le H
    push_cast
    linarith
  calc ((SP (r := r) (K := K) LL n0 B).ncard : ℝ) ≤ (((M + 1) ^ (N * (2 * N)) : ℕ) : ℝ) := by exact_mod_cast hle
    _ = ((M + 1 : ℕ) : ℝ) ^ (N * (2 * N)) := by push_cast; rfl
    _ ≤ (1 + 2 * a * (N : ℝ)) ^ (N * (2 * N)) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM1 _
    _ = Real.exp (2 * (N : ℝ) ^ 2 * ell0 N a) := by
        unfold ell0
        rw [← Real.exp_log hA, ← Real.exp_nat_mul, Real.log_exp]
        congr 1
        push_cast
        ring

end Formalism.MainNotions.SelectionLemmas.Pf.T
