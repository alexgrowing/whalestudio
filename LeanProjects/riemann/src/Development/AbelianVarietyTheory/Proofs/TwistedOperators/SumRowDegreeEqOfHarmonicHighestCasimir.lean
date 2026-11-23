import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ISupEigenspaceEqTop

open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.JointHarm

namespace GlobalTheory.HarmRowDegree

open GlobalTheory.Harm GlobalTheory.Harm.HighestUnique

private theorem sum_range_eq_sum_range_of_eventually_zero {n p : ℕ} (F : ℕ → ℤ) (hn : ∀ j, n ≤ j → F j = 0)
    (hp : ∀ j, p ≤ j → F j = 0) : ∑ j ∈ Finset.range n, F j = ∑ j ∈ Finset.range p, F j := by
  rcases le_total n p with h | h
  · exact Finset.sum_subset (Finset.range_mono h) fun j _ hj => hn j (by simpa using hj)
  · exact (Finset.sum_subset (Finset.range_mono h) fun j _ hj => hp j (by simpa using hj)).symm

theorem sum_pad {n p : ℕ} (f : Fin p → ℤ) (hf : ∀ i : Fin p, n ≤ i → f i = 0) :
    ∑ k : Fin n, (if h : (k : ℕ) < p then f ⟨k, h⟩ else 0) = ∑ k, f k := by
  have h1 : ∑ k : Fin n, (if h : (k : ℕ) < p then f ⟨k, h⟩ else 0) =
      ∑ j ∈ Finset.range n, (if h : j < p then f ⟨j, h⟩ else 0) :=
    Fin.sum_univ_eq_sum_range (fun j => if h : j < p then f ⟨j, h⟩ else 0) n
  have h2 : ∑ k : Fin p, f k = ∑ j ∈ Finset.range p, (if h : j < p then f ⟨j, h⟩ else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => if h : j < p then f ⟨j, h⟩ else 0) p]
    exact Finset.sum_congr rfl fun k _ => by simp
  rw [h1, h2]
  apply sum_range_eq_sum_range_of_eventually_zero
  · intro j hj
    by_cases h : j < p
    · simp only [h, dite_true]
      exact hf ⟨j, h⟩ hj
    · simp [h]
  · intro j hj
    simp [not_lt.mpr hj]

theorem sum_pad_rev {n q : ℕ} (f : Fin q → ℤ) (hf : ∀ i : Fin q, n ≤ i → f i = 0) :
    ∑ k : Fin n, (if h : n - 1 - (k : ℕ) < q then f ⟨n - 1 - k, h⟩ else 0) = ∑ k, f k := by
  calc ∑ k : Fin n, (if h : n - 1 - (k : ℕ) < q then f ⟨n - 1 - k, h⟩ else 0)
      = ∑ j ∈ Finset.range n, (fun j => if h : j < q then f ⟨j, h⟩ else 0) (n - 1 - j) :=
        Fin.sum_univ_eq_sum_range (fun j => (fun j => if h : j < q then f ⟨j, h⟩ else 0) (n - 1 - j)) n
    _ = ∑ j ∈ Finset.range n, (fun j => if h : j < q then f ⟨j, h⟩ else 0) j :=
        Finset.sum_range_reflect (fun j => if h : j < q then f ⟨j, h⟩ else 0) n
    _ = ∑ k : Fin n, (if h : (k : ℕ) < q then f ⟨k, h⟩ else 0) :=
        (Fin.sum_univ_eq_sum_range (fun j => if h : j < q then f ⟨j, h⟩ else 0) n).symm
    _ = ∑ k, f k := sum_pad f hf

private theorem sum_filter_lt_eq_sum_range_min (n i : ℕ) (G : ℕ → ℤ) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < i), G k =
      ∑ j ∈ Finset.range (min n i), G j := by
  rw [sum_filter_lt_eq_sum_range (fun k : Fin n => G k) i]
  have hs : Finset.range (min n i) = (Finset.range i).filter (fun j => j < n) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    exact And.comm
  rw [hs, Finset.sum_filter]
  exact Finset.sum_congr rfl fun j _ => by split_ifs <;> rfl

theorem sum_filter_pad' {n p : ℕ} (a : Fin p → ℕ) (ha : ∀ i : Fin p, n ≤ i → a i = 0) (i : ℕ) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < i),
      (if h : (k : ℕ) < p then (a ⟨k, h⟩ : ℤ) else 0) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin p => (j : ℕ) < min n i), (a j : ℤ) := by
  rw [sum_filter_lt_eq_sum_range (fun j : Fin p => (a j : ℤ)) (min n i)]
  exact sum_filter_lt_eq_sum_range_min n i (fun j => if h : j < p then (a ⟨j, h⟩ : ℤ) else 0)

private theorem sum_filter_not_lt_eq_sum_range_sub (n i : ℕ) (G : ℕ → ℤ) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin n => ¬ (k : ℕ) < i), G (n - 1 - k) =
      ∑ j ∈ Finset.range (n - i), G j := by
  rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun j => if ¬ j < i then G (n - 1 - j) else 0) n]
  rw [← Finset.sum_range_reflect (fun j => if ¬ j < i then G (n - 1 - j) else 0) n]
  rw [← Finset.sum_subset (Finset.range_mono (Nat.sub_le n i)) ?_]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    have e1 : ¬ (n - 1 - j < i) := by omega
    have e2 : n - 1 - (n - 1 - j) = j := by omega
    rw [if_pos e1, e2]
  · intro j hj hj'
    have h1 := Finset.mem_range.mp hj
    have h2 : ¬ j < n - i := fun h => hj' (Finset.mem_range.mpr h)
    have e1 : n - 1 - j < i := by omega
    rw [if_neg (not_not.mpr e1)]

theorem sum_filter_pad_rev' {n q : ℕ} (b : Fin q → ℕ) (hb : ∀ i : Fin q, n ≤ i → b i = 0)
    (i : ℕ) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin n => ¬ (k : ℕ) < i),
      (if h : n - 1 - (k : ℕ) < q then (b ⟨n - 1 - k, h⟩ : ℤ) else 0) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin q => (j : ℕ) < n - i), (b j : ℤ) := by
  rw [sum_filter_lt_eq_sum_range (fun j : Fin q => (b j : ℤ)) (n - i)]
  exact sum_filter_not_lt_eq_sum_range_sub n i (fun j => if h : j < q then (b ⟨j, h⟩ : ℤ) else 0)

private theorem casimir_sum_pad_eq_sum_range {n p : ℕ} (a : Fin p → ℕ) (ha : ∀ i : Fin p, n ≤ i → a i = 0) :
    ∑ i : Fin p, (a i : ℤ) * (a i + p - 1 - 2 * (i : ℕ)) + ((n : ℤ) - p) * ∑ i, (a i : ℤ) =
      ∑ j ∈ Finset.range n, (if h : j < p then (a ⟨j, h⟩ : ℤ) else 0) *
        ((if h : j < p then (a ⟨j, h⟩ : ℤ) else 0) + n - 1 - 2 * (j : ℤ)) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [sum_range_eq_sum_range_of_eventually_zero (p := p) _ ?_ ?_]
  · rw [← Fin.sum_univ_eq_sum_range (fun j => (if h : j < p then (a ⟨j, h⟩ : ℤ) else 0) *
      ((if h : j < p then (a ⟨j, h⟩ : ℤ) else 0) + n - 1 - 2 * (j : ℤ))) p]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.is_lt, dite_true, Fin.eta]
    ring
  · intro j hj
    by_cases h : j < p
    · simp [h, ha ⟨j, h⟩ hj]
    · simp [h]
  · intro j hj
    simp [not_lt.mpr hj]

private theorem casimir_sum_sub_reverse_eq_add_sum_range (n : ℕ) (A B : ℕ → ℤ) :
    ∑ k : Fin n, (A k - B (n - 1 - k)) * (A k - B (n - 1 - k) + n - 1 - 2 * ((k : ℕ) : ℤ)) +
        2 * ∑ k : Fin n, A k * B (n - 1 - k) =
      ∑ j ∈ Finset.range n, A j * (A j + n - 1 - 2 * (j : ℤ)) +
        ∑ j ∈ Finset.range n, B j * (B j + n - 1 - 2 * (j : ℤ)) := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (A j - B (n - 1 - j)) *
      (A j - B (n - 1 - j) + n - 1 - 2 * (j : ℤ))) n,
    Fin.sum_univ_eq_sum_range (fun j => A j * B (n - 1 - j)) n]
  rw [← Finset.sum_range_reflect (fun j => B j * (B j + n - 1 - 2 * (j : ℤ))) n]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  have e : ((n - 1 - j : ℕ) : ℤ) = (n : ℤ) - 1 - j := by omega
  rw [e]
  ring

theorem casimir_value_pad {n p q : ℕ} (a : Fin p → ℕ) (b : Fin q → ℕ)
    (ha : ∀ i : Fin p, n ≤ i → a i = 0) (hb : ∀ i : Fin q, n ≤ i → b i = 0) :
    (∑ i : Fin p, (a i : ℤ) * (a i + p - 1 - 2 * (i : ℕ)) + ((n : ℤ) - p) * ∑ i, (a i : ℤ)) +
      (∑ i : Fin q, (b i : ℤ) * (b i + q - 1 - 2 * (i : ℕ)) + ((n : ℤ) - q) * ∑ i, (b i : ℤ)) =
    ∑ k : Fin n, mixedWeight n a b k * (mixedWeight n a b k + n - 1 - 2 * (k : ℕ)) +
      2 * ∑ k : Fin n, (if h : (k : ℕ) < p then (a ⟨k, h⟩ : ℤ) else 0) *
        (if h : n - 1 - (k : ℕ) < q then (b ⟨n - 1 - k, h⟩ : ℤ) else 0) := by
  rw [casimir_sum_pad_eq_sum_range a ha, casimir_sum_pad_eq_sum_range b hb]
  simp only [mixedWeight_apply]
  exact (casimir_sum_sub_reverse_eq_add_sum_range n (fun j => if h : j < p then (a ⟨j, h⟩ : ℤ) else 0)
    (fun j => if h : j < q then (b ⟨j, h⟩ : ℤ) else 0)).symm

theorem row_degree_eq_zero {K σ : Type*} [Field K] [CharZero K] [DecidableEq σ] {p n : ℕ}
    (z : Fin p × Fin n → σ) (hz : Function.Injective z) {P : MvPolynomial σ K} (hP : P ≠ 0)
    (a : Fin p → ℕ) (hrow : ∀ i, ∀ m ∈ P.support, ∑ k, m (z (i, k)) = a i)
    (hinv : ∀ i j : Fin p, i < j → ∀ t : K,
      bind₁ (fun s => X s + ∑ k, if s = z (j, k) then C t * X (z (i, k)) else 0) P = P)
    (i : Fin p) (hi : n ≤ i) : a i = 0 := by
  obtain ⟨m, hm⟩ : P.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr fun h => hP (MvPolynomial.support_eq_empty.mp h)
  have h := column_degree_le z hz P a hrow hinv Finset.univ m hm
  rw [Finset.card_univ, Fintype.card_fin] at h
  have hsum : ∑ j, ∑ k ∈ Finset.univ, m (z (j, k)) = ∑ j, a j :=
    Finset.sum_congr rfl fun j _ => hrow j m hm
  rw [hsum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin p => (j : ℕ) < n)] at h
  have h2 : ∑ j ∈ Finset.univ.filter (fun j : Fin p => ¬ (j : ℕ) < n), a j = 0 := by omega
  exact (Finset.sum_eq_zero_iff.mp h2) i (by simp [hi])

theorem sum_row_degree_eq : ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (k l n : ℕ) (z : Fin k × Fin n → σ) (y : Fin l × Fin n → σ), Function.Injective z → Function.Injective y → (∀ u w, z u ≠ y w) → ∀ (P : MvPolynomial σ ℂ) (a : Fin k → ℕ) (b : Fin l → ℕ) (κ : Fin n → ℤ), P ≠ 0 → Antitone a → Antitone b → Antitone κ → (∀ i j, i < j → rowOp ℂ z i j P = 0) → (∀ i, rowOp ℂ z i i P = (a i : ℂ) • P) → (∀ i j, i < j → rowOp ℂ y i j P = 0) → (∀ i, rowOp ℂ y i i P = (b i : ℂ) • P) → (∀ i j, ∑ t, pderiv (z (i, t)) (pderiv (y (j, t)) P) = 0) → (∀ i j, i < j → mixedOp ℂ z y i j P = 0) → (∀ t, mixedOp ℂ z y t t P = (κ t : ℂ) • P) → ∑ i, (a i : ℤ) = ∑ t, max (κ t) 0 := by
  intro σ _ _ k l n z y hz hy hzy P a b κ hP ha hb hκ hzu hzd hyu hyd hharm hup hwt
  have hrz : ∀ i, ∀ m ∈ P.support, ∑ t, m (z (i, t)) = a i := fun i m hm => by
    have := (rowOp_eq_smul_iff z i P (a i : ℂ)).mp (hzd i) m hm
    exact_mod_cast this
  have hry : ∀ i, ∀ m ∈ P.support, ∑ t, m (y (i, t)) = b i := fun i m hm => by
    have := (rowOp_eq_smul_iff y i P (b i : ℂ)).mp (hyd i) m hm
    exact_mod_cast this
  have hiz : ∀ i j : Fin k, i < j → ∀ t : ℂ,
      bind₁ (fun s => X s + ∑ t', if s = z (j, t') then C t * X (z (i, t')) else 0) P = P := by
    intro i j hij
    have hw : Function.Injective fun t : Fin n => z (j, t) := fun t t' h => by
      simpa using hz h
    have huw : ∀ t t' : Fin n, z (i, t) ≠ z (j, t') := fun t t' h => by
      have := hz h
      simp only [Prod.mk.injEq] at this
      exact (ne_of_lt hij) this.1
    have := (rowAdd_invariant_iff (K := ℂ) (fun t => z (i, t)) (fun t => z (j, t)) hw huw P).out 1 2
    exact this.mpr ((rowOp_apply z i j P).symm.trans (hzu i j hij))
  have hiy : ∀ i j : Fin l, i < j → ∀ t : ℂ,
      bind₁ (fun s => X s + ∑ t', if s = y (j, t') then C t * X (y (i, t')) else 0) P = P := by
    intro i j hij
    have hw : Function.Injective fun t : Fin n => y (j, t) := fun t t' h => by
      simpa using hy h
    have huw : ∀ t t' : Fin n, y (i, t) ≠ y (j, t') := fun t t' h => by
      have := hy h
      simp only [Prod.mk.injEq] at this
      exact (ne_of_lt hij) this.1
    have := (rowAdd_invariant_iff (K := ℂ) (fun t => y (i, t)) (fun t => y (j, t)) hw huw P).out 1 2
    exact this.mpr ((rowOp_apply y i j P).symm.trans (hyu i j hij))
  have ha0 : ∀ i : Fin k, n ≤ i → a i = 0 := row_degree_eq_zero z hz hP a hrz hiz
  have hb0 : ∀ i : Fin l, n ≤ i → b i = 0 := row_degree_eq_zero y hy hP b hry hiy
  have hC1 := casimir_on_highest (mixedOp ℂ z y) (mixedOp_lie z hz y hy hzy) P κ hup hwt
  have hC2 := casimir_mixedOp z hz y hy hzy P
  have hcross : ∑ i, ∑ j, (∑ t, X (z (i, t)) * X (y (j, t))) *
      ∑ t, pderiv (z (i, t)) (pderiv (y (j, t)) P) = (0 : MvPolynomial σ ℂ) := by
    simp [hharm]
  rw [casimir_rows z hz a hrz hiz, casimir_rows y hy b hry hiy, hcross, smul_zero, sub_zero,
    ← add_smul] at hC2
  have hCint : ∑ i, κ i * (κ i + n - 1 - 2 * (i : ℕ)) =
      (∑ i : Fin k, (a i : ℤ) * (a i + k - 1 - 2 * (i : ℕ)) + ((n : ℤ) - k) * ∑ i, (a i : ℤ)) +
      (∑ i : Fin l, (b i : ℤ) * (b i + l - 1 - 2 * (i : ℕ)) + ((n : ℤ) - l) * ∑ i, (b i : ℤ)) := by
    have := smul_left_injective ℂ hP (hC1.symm.trans hC2)
    exact_mod_cast this
  have hpad := casimir_value_pad a b ha0 hb0
  have hpair : 0 ≤ ∑ t : Fin n, (if h : (t : ℕ) < k then (a ⟨t, h⟩ : ℤ) else 0) * (if h : n - 1 - (t : ℕ) < l then (b ⟨n - 1 - t, h⟩ : ℤ) else 0) :=
    Finset.sum_nonneg fun t _ => mul_nonneg (by split_ifs <;> simp) (by split_ifs <;> simp)
  obtain ⟨m, hm⟩ : P.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr fun h => hP (MvPolynomial.support_eq_empty.mp h)
  have hw : ∀ t, ∑ j, (m (z (j, t)) : ℤ) - ∑ j, (m (y (j, t)) : ℤ) = κ t := fun t => weight_of_mem_support z y (hwt t) hm
  have hzs : ∑ t, ∑ j, (m (z (j, t)) : ℤ) = ∑ i, (a i : ℤ) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => by exact_mod_cast hrz i m hm
  have hys : ∑ t, ∑ j, (m (y (j, t)) : ℤ) = ∑ i, (b i : ℤ) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => by exact_mod_cast hry i m hm
  have hcard : ∀ i : ℕ, (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)).card = min n i := by
    intro i
    have e : (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)).map Fin.valEmbedding = Finset.range (min n i) := by
      ext j
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply, Finset.mem_range, lt_min_iff]
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t.isLt, ht⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨j, h1⟩, h2, rfl⟩
    rw [← Finset.card_map Fin.valEmbedding, e, Finset.card_range]
  have hcard' : ∀ i : ℕ, (Finset.univ.filter (fun t : Fin n => ¬ (t : ℕ) < i)).card = n - i := by
    intro i
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun t : Fin n => (t : ℕ) < i)
    rw [hcard i, Finset.card_univ, Fintype.card_fin] at h
    omega
  have hb0' : ∀ j : Fin l, n ≤ j → (b j : ℤ) = 0 := fun j hj => by simp [hb0 j hj]
  have ha0' : ∀ j : Fin k, n ≤ j → (a j : ℤ) = 0 := fun j hj => by simp [ha0 j hj]
  have hle : ∀ i : ℕ, ∑ t ∈ (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)), κ t ≤ ∑ t ∈ (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)), mixedWeight n a b t := by
    intro i
    have f1 : ∑ t ∈ (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)), κ t = ∑ t ∈ (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)), ∑ j, (m (z (j, t)) : ℤ) - ∑ t ∈ (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)), ∑ j, (m (y (j, t)) : ℤ) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun t _ => (hw t).symm
    have f2 : ∑ t ∈ (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)), ∑ j, (m (z (j, t)) : ℤ) ≤
        ∑ j ∈ Finset.univ.filter (fun j : Fin k => (j : ℕ) < min n i), (a j : ℤ) := by
      have h := column_degree_le z hz P a hrz hiz (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)) m hm
      rw [hcard i] at h
      rw [Finset.sum_comm]
      exact_mod_cast h
    have f3 : ∑ t ∈ (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)), ∑ j, (m (y (j, t)) : ℤ) + ∑ t ∈ (Finset.univ.filter (fun t : Fin n => ¬ (t : ℕ) < i)), ∑ j, (m (y (j, t)) : ℤ) = ∑ j, (b j : ℤ) := by
      rw [Finset.sum_filter_add_sum_filter_not, hys]
    have f4 : ∑ t ∈ (Finset.univ.filter (fun t : Fin n => ¬ (t : ℕ) < i)), ∑ j, (m (y (j, t)) : ℤ) ≤
        ∑ j ∈ Finset.univ.filter (fun j : Fin l => (j : ℕ) < n - i), (b j : ℤ) := by
      have h := column_degree_le y hy P b hry hiy (Finset.univ.filter (fun t : Fin n => ¬ (t : ℕ) < i)) m hm
      rw [hcard' i] at h
      rw [Finset.sum_comm]
      exact_mod_cast h
    have f5 : ∑ t ∈ (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)), mixedWeight n a b t = ∑ t ∈ (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)), (if h : (t : ℕ) < k then (a ⟨t, h⟩ : ℤ) else 0) - ∑ t ∈ (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)), (if h : n - 1 - (t : ℕ) < l then (b ⟨n - 1 - t, h⟩ : ℤ) else 0) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun t _ => mixedWeight_apply n a b t
    have f6 := sum_filter_pad' a ha0 i
    have f7 : ∑ t ∈ (Finset.univ.filter (fun t : Fin n => (t : ℕ) < i)), (if h : n - 1 - (t : ℕ) < l then (b ⟨n - 1 - t, h⟩ : ℤ) else 0) + ∑ t ∈ (Finset.univ.filter (fun t : Fin n => ¬ (t : ℕ) < i)), (if h : n - 1 - (t : ℕ) < l then (b ⟨n - 1 - t, h⟩ : ℤ) else 0) = ∑ j, (b j : ℤ) := by
      rw [Finset.sum_filter_add_sum_filter_not]
      exact sum_pad_rev (fun j => (b j : ℤ)) hb0'
    have f8 := sum_filter_pad_rev' b hb0 i
    linarith
  have hsum : ∑ t, κ t = ∑ t, mixedWeight n a b t := by
    have e1 : ∑ t, κ t = ∑ i, (a i : ℤ) - ∑ j, (b j : ℤ) := by
      rw [← hzs, ← hys, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun t _ => (hw t).symm
    have e2 : ∑ t, mixedWeight n a b t = ∑ t : Fin n, (if h : (t : ℕ) < k then (a ⟨t, h⟩ : ℤ) else 0) - ∑ t : Fin n, (if h : n - 1 - (t : ℕ) < l then (b ⟨n - 1 - t, h⟩ : ℤ) else 0) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun t _ => mixedWeight_apply n a b t
    rw [e1, e2, sum_pad (fun j => (a j : ℤ)) ha0', sum_pad_rev (fun j => (b j : ℤ)) hb0']
  have hCle : ∑ t, mixedWeight n a b t * (mixedWeight n a b t + n - 1 - 2 * (t : ℕ)) ≤
      ∑ t, κ t * (κ t + n - 1 - 2 * (t : ℕ)) := by
    linarith
  have hκμ : κ = mixedWeight n a b :=
    casimir_value_strict κ (mixedWeight n a b) hκ (antitone_mixedWeight n ha hb) hle hsum hCle
  subst hκμ
  have hpair0 : ∑ t : Fin n, (if h : (t : ℕ) < k then (a ⟨t, h⟩ : ℤ) else 0) * (if h : n - 1 - (t : ℕ) < l then (b ⟨n - 1 - t, h⟩ : ℤ) else 0) = 0 := by linarith
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun t _ =>
    mul_nonneg (by split_ifs <;> simp) (by split_ifs <;> simp))).mp hpair0
  rw [← sum_pad (fun j => (a j : ℤ)) ha0']
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [mixedWeight_apply]
  have hA : 0 ≤ (if h : (t : ℕ) < k then (a ⟨t, h⟩ : ℤ) else 0) := by split_ifs <;> simp
  have hB : 0 ≤ (if h : n - 1 - (t : ℕ) < l then (b ⟨n - 1 - t, h⟩ : ℤ) else 0) := by split_ifs <;> simp
  rcases mul_eq_zero.mp (hterm t ht) with h | h
  · rw [h, zero_sub, max_eq_right (by linarith)]
  · rw [h, sub_zero, max_eq_left hA]

end GlobalTheory.HarmRowDegree
