import Formalism.GradedWeylDivisibility.FinalD

open MvPolynomial Formalism.GradedWeylDivisibility

private theorem sum_ite_eq_of_shifted_index {n m : ℕ} (g : Fin m → Fin n) (hg : ∀ p, (g p : ℕ) = n - m + p)
    (hm : m ≤ n) (i : Fin n) :
    (∑ p : Fin m, if g p = i then 1 else 0 : ℕ) = if n - m ≤ (i : ℕ) then 1 else 0 := by
  by_cases h : n - m ≤ (i : ℕ)
  · rw [if_pos h, Finset.sum_eq_single (⟨i - (n - m), by have := i.isLt; omega⟩ : Fin m)]
    · rw [if_pos]
      ext
      rw [hg]
      show n - m + ((i : ℕ) - (n - m)) = (i : ℕ)
      omega
    · intro p _ hp
      rw [if_neg]
      intro he
      apply hp
      ext
      have := hg p
      rw [he] at this
      show (p : ℕ) = (i : ℕ) - (n - m)
      omega
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro p _
    rw [if_neg]
    intro he
    apply h
    have := hg p
    rw [he] at this
    omega

private theorem sum_ite_pair_castLE_eq_of_shifted_index {n m : ℕ} (hm : m ≤ n) (g : Fin m → Fin n)
    (hg : ∀ p, (g p : ℕ) = n - m + p) (i j : Fin n) :
    (∑ p : Fin m, if (g p, Fin.castLE hm p) = (i, j) then 1 else 0 : ℕ)
      = if m + (i : ℕ) = n + j then 1 else 0 := by
  by_cases h : m + (i : ℕ) = n + j
  · rw [if_pos h, Finset.sum_eq_single (⟨j, by have := i.isLt; omega⟩ : Fin m)]
    · rw [if_pos]
      refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
      · show ((g _ : Fin n) : ℕ) = (i : ℕ)
        rw [hg]
        show n - m + (j : ℕ) = (i : ℕ)
        omega
      · simp
    · intro p _ hp
      rw [if_neg]
      intro he
      apply hp
      ext
      have := congrArg (fun x => (x.2 : ℕ)) he
      simp only [Fin.coe_castLE] at this
      show (p : ℕ) = (j : ℕ)
      exact this
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro p _
    rw [if_neg]
    intro he
    apply h
    have h1 := congrArg (fun x => (x.1 : ℕ)) he
    have h2 := congrArg (fun x => (x.2 : ℕ)) he
    simp only [Fin.coe_castLE] at h1 h2
    rw [hg] at h1
    have := p.isLt
    omega

private theorem strictMono_apply_add_le {n m : ℕ} (f : Fin m → Fin n) (hf : StrictMono f) (p : Fin m) :
    (f p : ℕ) + m ≤ n + p := by
  have h1 := Finset.card_le_card_of_injOn f (s := Finset.Ici p) (t := Finset.Ici (f p))
    (by
      intro q hq
      simp only [Finset.coe_Ici, Set.mem_Ici, Finset.mem_Ici] at hq ⊢
      exact hf.monotone hq)
    (fun a _ b _ h => hf.injective h)
  simp only [Fin.card_Ici] at h1
  have := p.isLt
  have := (f p).isLt
  omega

private theorem sum_mul_count_eq_sum_sum_apply {n K : ℕ} (sz : Fin K → ℕ) (f : ∀ k, Fin (sz k) → Fin n)
    (a : Fin n → ℤ) :
    ∑ i, a i * ((∑ k, ∑ p : Fin (sz k), if f k p = i then 1 else 0 : ℕ) : ℤ)
      = ∑ k, ∑ p, a (f k p) := by
  push_cast
  simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp

private theorem rowWt_bidetExp_eq_count {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin n) (i : Fin n) :
    rowWt (bidetExp sz hsz I) i = ∑ k, ∑ p : Fin (sz k), if I k p = i then 1 else 0 := by
  simp only [rowWt, rowDeg, bidetExp, Finsupp.finset_sum_apply, Finsupp.single_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Prod.mk.injEq]
  by_cases h : I k p = i
  · simp [h]
  · simp [h]

private theorem shapeDeg_rev_eq_count_of_shifted {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (J : ∀ k, Fin (sz k) → Fin n) (hJ : ∀ k p, (J k p : ℕ) = n - sz k + p) (i : Fin n) :
    shapeDeg sz (Fin.rev i) = ∑ k, ∑ p : Fin (sz k), if J k p = i then 1 else 0 := by
  rw [Finset.sum_congr rfl fun k _ => sum_ite_eq_of_shifted_index (J k) (hJ k) (hsz k) i, shapeDeg,
    Finset.card_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fin.val_rev]
  have := i.isLt
  by_cases h : n - sz k ≤ (i : ℕ)
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

private theorem bidetExp_apply_eq_card_of_canonical {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin n) (hcan : ∀ k p, (I k p : ℕ) + sz k = n + p) (i j : Fin n) :
    bidetExp sz hsz I (i, j) = (Finset.univ.filter fun k => sz k + (i : ℕ) = n + j).card := by
  simp only [bidetExp, Finsupp.finset_sum_apply, Finsupp.single_apply]
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact sum_ite_pair_castLE_eq_of_shifted_index (hsz k) (I k) (fun p => by have := hcan k p; have := hsz k; omega) i j

private theorem card_lt_eq_card_eq_succ_add_card_succ_lt {K : ℕ} (s : Fin K → ℕ) (t : ℕ) :
    (Finset.univ.filter fun k => t < s k).card
      = (Finset.univ.filter fun k => s k = t + 1).card
        + (Finset.univ.filter fun k => t + 1 < s k).card := by
  simp only [Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> omega

theorem UpperTheory.bideterminant_row_weight_dominance :
    ∀ (n K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin n), (∀ k, StrictMono (I k)) → (∀ a : Fin n → ℤ, Antitone a → ∑ i, a i * (shapeDeg sz (Fin.rev i) : ℤ) ≤ ∑ i, a i * (rowWt (bidetExp sz hsz I) i : ℤ)) ∧ (∑ i : Fin n, ((n : ℤ) - 1 - (i : ℕ)) * (rowWt (bidetExp sz hsz I) i : ℤ) ≤ ∑ i : Fin n, ((n : ℤ) - 1 - (i : ℕ)) * (shapeDeg sz (Fin.rev i) : ℤ) → ∀ k p, (I k p : ℕ) + sz k = n + p) ∧ ((∀ k p, (I k p : ℕ) + sz k = n + p) → (∀ i, rowWt (bidetExp sz hsz I) i = shapeDeg sz (Fin.rev i)) ∧ ∀ (K' : ℕ) (sz' : Fin K' → ℕ) (hsz' : ∀ k, sz' k ≤ n) (I' : ∀ k, Fin (sz' k) → Fin n), (∀ k p, (I' k p : ℕ) + sz' k = n + p) → (shapeDeg sz' : Fin n → ℕ) = shapeDeg sz → bidetExp sz' hsz' I' = bidetExp sz hsz I) := by
  intro n K sz hsz I hI
  obtain ⟨J, hJ⟩ : ∃ J : ∀ k, Fin (sz k) → Fin n, ∀ k p, (J k p : ℕ) = n - sz k + p :=
    ⟨fun k p => ⟨n - sz k + p, by have := p.isLt; have := hsz k; omega⟩, fun _ _ => rfl⟩
  have hrow := rowWt_bidetExp_eq_count sz hsz I
  have hsh := shapeDeg_rev_eq_count_of_shifted sz hsz J hJ
  have hle : ∀ k p, (I k p : ℕ) + sz k ≤ n + p := fun k p => strictMono_apply_add_le (I k) (hI k) p
  have hws : ∀ a : Fin n → ℤ, ∑ i, a i * (shapeDeg sz (Fin.rev i) : ℤ) = ∑ k, ∑ p, a (J k p) := by
    intro a
    simp only [hsh]
    exact sum_mul_count_eq_sum_sum_apply sz J a
  have hwr : ∀ a : Fin n → ℤ,
      ∑ i, a i * (rowWt (bidetExp sz hsz I) i : ℤ) = ∑ k, ∑ p, a (I k p) := by
    intro a
    simp only [hrow]
    exact sum_mul_count_eq_sum_sum_apply sz I a
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rw [hws, hwr]
    refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun p _ => ha ?_
    rw [Fin.le_iff_val_le_val, hJ]
    have := hle k p
    have := hsz k
    omega
  · intro h k p
    have e1 := hws (fun i : Fin n => (n : ℤ) - 1 - ((i : ℕ) : ℤ))
    have e2 := hwr (fun i : Fin n => (n : ℤ) - 1 - ((i : ℕ) : ℤ))
    beta_reduce at e1 e2
    rw [e1, e2] at h
    by_contra hne
    refine absurd h (not_le.2 ?_)
    apply Finset.sum_lt_sum
    · intro k' _
      apply Finset.sum_le_sum
      intro p' _
      have := hle k' p'
      have := hJ k' p'
      have := hsz k'
      omega
    · refine ⟨k, Finset.mem_univ _, Finset.sum_lt_sum (fun p' _ => ?_) ⟨p, Finset.mem_univ _, ?_⟩⟩
      · have := hle k p'
        have := hJ k p'
        have := hsz k
        omega
      · have := hle k p
        have := hJ k p
        have := hsz k
        omega
  · intro hcan
    have hIJ : I = J := by
      funext k p
      ext
      rw [hJ]
      have := hcan k p
      have := hsz k
      omega
    refine ⟨fun i => by rw [hrow i, hsh i, hIJ], ?_⟩
    intro K' sz' hsz' I' hcan' hshape
    ext x
    obtain ⟨i, j⟩ := x
    rw [bidetExp_apply_eq_card_of_canonical sz' hsz' I' hcan' i j, bidetExp_apply_eq_card_of_canonical sz hsz I hcan i j]
    have hc : ∀ t : ℕ, (Finset.univ.filter fun k => t < sz' k).card
        = (Finset.univ.filter fun k => t < sz k).card := by
      intro t
      by_cases ht : t < n
      · have := congrFun hshape ⟨t, ht⟩
        simpa only [shapeDeg, Fin.val_mk] using this
      · have e1 : (Finset.univ.filter fun k => t < sz' k) = ∅ :=
          Finset.filter_eq_empty_iff.2 fun k _ => by have := hsz' k; omega
        have e2 : (Finset.univ.filter fun k => t < sz k) = ∅ :=
          Finset.filter_eq_empty_iff.2 fun k _ => by have := hsz k; omega
        rw [e1, e2, Finset.card_empty, Finset.card_empty]
    have e1 : (Finset.univ.filter fun k => sz' k + (i : ℕ) = n + j)
        = Finset.univ.filter fun k => sz' k = (n + j - i - 1) + 1 :=
      Finset.filter_congr fun k _ => by have := i.isLt; omega
    have e2 : (Finset.univ.filter fun k => sz k + (i : ℕ) = n + j)
        = Finset.univ.filter fun k => sz k = (n + j - i - 1) + 1 :=
      Finset.filter_congr fun k _ => by have := i.isLt; omega
    rw [e1, e2]
    have h1 := card_lt_eq_card_eq_succ_add_card_succ_lt sz' (n + j - i - 1)
    have h2 := card_lt_eq_card_eq_succ_add_card_succ_lt sz (n + j - i - 1)
    have h3 := hc (n + j - i - 1)
    have h4 := hc (n + j - i - 1 + 1)
    omega
