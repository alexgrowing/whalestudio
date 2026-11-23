import Mathlib

private lemma val_nat_le_one {L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation L Γ) (m : ℕ) : w (m : L) ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_succ]
    exact w.map_add_le ih (by simp)

private lemma exists_peak {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (n : ℕ) (t : ℕ → Γ)
    (h0 : ∀ k ≤ n, 0 < t k) (hc : ∀ k, k + 2 ≤ n → t k * t (k + 2) < t (k + 1) * t (k + 1)) :
    ∃ j ≤ n, ∀ k ≤ n, k ≠ j → k + 1 ≠ j → t k < t j := by
  classical
  have hex : ∃ j, n ≤ j ∨ t (j + 1) < t j := ⟨n, Or.inl le_rfl⟩
  set j := Nat.find hex with hj
  have hjn : j ≤ n := Nat.find_min' hex (Or.inl le_rfl)
  have hlo : ∀ k < j, t k ≤ t (k + 1) := fun k hk =>
    not_lt.1 fun h => Nat.find_min hex hk (Or.inr h)
  have hlo' : ∀ k, k + 1 < j → t k < t (k + 1) := by
    intro k hk
    have h1 := hc k (by omega)
    have h2 : t (k + 1) * t (k + 1) ≤ t (k + 1) * t (k + 2) :=
      mul_le_mul_of_nonneg_left (hlo (k + 1) hk) zero_le
    exact lt_of_mul_lt_mul_right (h1.trans_le h2) zero_le
  have hhi : ∀ k, j ≤ k → k < n → t (k + 1) < t k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro h
      rcases Nat.find_spec hex with h' | h'
      · omega
      · exact h'
    | succ k hk ih =>
      intro h
      have h1 := hc k (by omega)
      have h2 : t (k + 1) * t (k + 1) ≤ t k * t (k + 1) :=
        mul_le_mul_of_nonneg_right (ih (by omega)).le zero_le
      exact lt_of_mul_lt_mul_left (h1.trans_le h2) zero_le
  have hle : ∀ k ≤ j, t k ≤ t j := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self => exact le_rfl
    | of_succ k hk ih => exact (hlo k hk).trans ih
  have hgt : ∀ k, j + 1 ≤ k → k ≤ n → t k < t j := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro h; exact hhi j le_rfl (by omega)
    | succ k hk ih => intro h; exact (hhi k (by omega) (by omega)).trans (ih (by omega))
  refine ⟨j, hjn, fun k hk h1 h2 => ?_⟩
  rcases lt_or_gt_of_ne h1 with h | h
  · exact (hlo' k (by omega)).trans_le (hle _ (by omega))
  · exact hgt k h hk

private lemma no_double_zero {L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation L Γ) (n : ℕ) (b : ℕ → L) (h0 : ∀ k ≤ n, b k ≠ 0)
    (hc : ∀ k, k + 2 ≤ n → w (b k * b (k + 2)) < w (b (k + 1) * b (k + 1)))
    (h1 : ∑ k ∈ Finset.range (n + 1), b k = 0)
    (h2 : ∑ k ∈ Finset.range (n + 1), (k : L) * b k = 0) : False := by
  have hpos : ∀ k ≤ n, 0 < w (b k) := fun k hk => zero_lt_iff.2 ((map_ne_zero w).2 (h0 k hk))
  obtain ⟨j, hjn, hj⟩ := exists_peak n (fun k => w (b k)) hpos
    (fun k hk => by simpa only [map_mul] using hc k hk)
  have hs : ∑ k ∈ Finset.range (n + 1), (((k + 1 : ℕ) : L) - (j : L)) * b k = 0 := by
    have : ∀ k : ℕ, (((k + 1 : ℕ) : L) - (j : L)) * b k = (k : L) * b k + (1 - (j : L)) * b k := by
      intro k; push_cast; ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2, mul_zero, add_zero]
  have hjj : (((j + 1 : ℕ) : L) - (j : L)) * b j = b j := by push_cast; ring
  have key := w.map_sum_eq_of_lt (s := Finset.range (n + 1))
    (f := fun k => (((k + 1 : ℕ) : L) - (j : L)) * b k) (j := j)
    (Finset.mem_range.2 (by omega)) (by
      intro k hk
      rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hk
      rw [hjj]
      by_cases hkj : k + 1 = j
      · rw [hkj, sub_self, zero_mul, map_zero]
        exact hpos j hjn
      · rw [map_mul]
        refine lt_of_le_of_lt ?_ (hj k (by omega) hk.2 hkj)
        exact mul_le_of_le_one_left zero_le
          (w.map_sub_le (val_nat_le_one w _) (val_nat_le_one w _)))
  rw [hs, hjj, map_zero] at key
  exact (hpos j hjn).ne key

private lemma exists_extension {K L Γ : Type} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (f : K →+* L) :
    ∃ A : ValuationSubring L, ∀ x y : K, v x < v y → A.valuation (f x) < A.valuation (f y) := by
  obtain ⟨A, h, hA⟩ := IsLocalRing.exists_factor_valuationRing
    (f.comp v.valuationSubring.subtype)
  refine ⟨A, fun x y hxy => ?_⟩
  have hy : 0 < v y := lt_of_le_of_lt zero_le hxy
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy
  have hlt : v (x / y) < 1 := by
    rw [map_div₀]
    exact (div_lt_one₀ hy).2 hxy
  let z : v.valuationSubring := ⟨x / y, hlt.le⟩
  have hz : z ∈ IsLocalRing.maximalIdeal v.valuationSubring :=
    (Valuation.mem_maximalIdeal_iff _ _).2 hlt
  haveI : IsLocalRing A.toSubring := inferInstanceAs (IsLocalRing A)
  have hz' := (A.valuation_lt_one_iff _).1 (map_nonunit
    ((f.comp v.valuationSubring.subtype).codRestrict A.toSubring h) z hz)
  have hz'' : A.valuation (f (x / y)) < 1 := hz'
  rw [map_div₀, map_div₀] at hz''
  exact (div_lt_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 ((map_ne_zero f).2 hy0)))).1 hz''

private lemma tail_succ {Γ : Type} [CommMonoid Γ] {n : ℕ} (γ : Fin n → Γ) (k : ℕ) (hk : k < n) :
    ∏ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), γ i =
      γ ⟨k, hk⟩ * ∏ i ∈ Finset.univ.filter (fun i : Fin n => k + 1 ≤ i.val), γ i := by
  rw [← Finset.prod_insert (by simp)]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
  omega

theorem UpperTheory.separable_of_newton_polygon :
    ∀ {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (n : ℕ) (γ : Fin n → Γ),
        StrictMono γ → (∀ i, γ i ≠ 0) → ∀ p : Polynomial K, p.Monic → p.natDegree = n →
        (∀ k ≤ n, v (p.coeff k) = ∏ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), γ i) → p.Separable := by
  intro K Γ _ _ v n γ hγ hγ0 p _ hn hv
  have hv0 : ∀ k ≤ n, v (p.coeff k) ≠ 0 := fun k hk => by
    rw [hv k hk]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hγ0 i
  have ha0 : ∀ k ≤ n, p.coeff k ≠ 0 := fun k hk => (map_ne_zero v).1 (hv0 k hk)
  have hstep : ∀ k (hk : k < n), v (p.coeff k) = γ ⟨k, hk⟩ * v (p.coeff (k + 1)) := fun k hk => by
    rw [hv k hk.le, hv (k + 1) hk, tail_succ γ k hk]
  have hconc : ∀ k, k + 2 ≤ n →
      v (p.coeff k * p.coeff (k + 2)) < v (p.coeff (k + 1) * p.coeff (k + 1)) := by
    intro k hk
    have e1 := hstep k (by omega)
    have e2 := hstep (k + 1) (by omega)
    have hlt : γ ⟨k, by omega⟩ < γ ⟨k + 1, by omega⟩ := hγ (by simp [Fin.lt_def])
    have hp : 0 < v (p.coeff (k + 1)) * v (p.coeff (k + 2)) :=
      mul_pos (zero_lt_iff.2 (hv0 _ (by omega))) (zero_lt_iff.2 (hv0 _ hk))
    calc v (p.coeff k * p.coeff (k + 2))
        = γ ⟨k, by omega⟩ * (v (p.coeff (k + 1)) * v (p.coeff (k + 2))) := by
          rw [map_mul, e1, mul_assoc]
      _ < γ ⟨k + 1, by omega⟩ * (v (p.coeff (k + 1)) * v (p.coeff (k + 2))) :=
          mul_lt_mul_of_pos_right hlt hp
      _ = v (p.coeff (k + 1) * p.coeff (k + 1)) := by
          rw [map_mul, mul_left_comm, ← e2]
  rw [Polynomial.separable_def,
    Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K (AlgebraicClosure K)]
  intro r
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨hp, hd⟩ := hcon
  set f := algebraMap K (AlgebraicClosure K) with hf
  obtain ⟨A, hA⟩ := exists_extension v f
  have hr : r ≠ 0 := by
    rintro rfl
    rw [← Polynomial.coeff_zero_eq_aeval_zero'] at hp
    exact ha0 0 (Nat.zero_le _) ((map_eq_zero _).1 hp)
  refine no_double_zero A.valuation n (fun k => f (p.coeff k) * r ^ k)
    (fun k hk => mul_ne_zero ((map_ne_zero f).2 (ha0 k hk)) (pow_ne_zero _ hr)) ?_ ?_ ?_
  · intro k hk
    have e1 : f (p.coeff k) * r ^ k * (f (p.coeff (k + 2)) * r ^ (k + 2)) =
        f (p.coeff k * p.coeff (k + 2)) * r ^ (2 * k + 2) := by rw [map_mul]; ring
    have e2 : f (p.coeff (k + 1)) * r ^ (k + 1) * (f (p.coeff (k + 1)) * r ^ (k + 1)) =
        f (p.coeff (k + 1) * p.coeff (k + 1)) * r ^ (2 * k + 2) := by rw [map_mul]; ring
    rw [e1, e2, map_mul A.valuation, map_mul A.valuation]
    exact mul_lt_mul_of_pos_right (hA _ _ (hconc k hk))
      (zero_lt_iff.2 ((map_ne_zero _).2 (pow_ne_zero _ hr)))
  · rw [Polynomial.aeval_eq_sum_range, hn] at hp
    simpa only [Algebra.smul_def] using hp
  · have hX : Polynomial.aeval r (Polynomial.derivative p * Polynomial.X) = 0 := by rw [map_mul, hd, zero_mul]
    have hcoeff : ∀ k : ℕ, (Polynomial.derivative p * Polynomial.X).coeff k = (k : K) * p.coeff k := by
      intro k
      cases k with
      | zero => simp
      | succ k => rw [Polynomial.coeff_mul_X, Polynomial.coeff_derivative]; push_cast; ring
    have hdeg : (Polynomial.derivative p * Polynomial.X).natDegree < n + 1 := by
      rw [Nat.lt_succ_iff, Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [hcoeff, Polynomial.coeff_eq_zero_of_natDegree_lt (hn ▸ hk), mul_zero]
    rw [Polynomial.aeval_eq_sum_range' hdeg] at hX
    simpa only [hcoeff, Algebra.smul_def, map_mul, map_natCast, mul_assoc] using hX
