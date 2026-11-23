import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTupleC

noncomputable section

namespace PI.WGL.LTD

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC

theorem sum_ite_val {n : ℕ} (f : Fin n → ℕ) (j : ℕ) :
    (∑ i : Fin n, if i.1 = j then f i else 0) = if h : j < n then f ⟨j, h⟩ else 0 := by
  split_ifs with hj
  · rw [Finset.sum_eq_single ⟨j, hj⟩]
    · simp
    · intro i _ hi; rw [if_neg]; intro h'; exact hi (Fin.ext h')
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · apply Finset.sum_eq_zero; intro i _; rw [if_neg]; intro h'; exact hj (h' ▸ i.2)

theorem natW_sg_val {n : ℕ} (sg : DomWeight n) (i : Fin n) :
    ((sg.natW i : ℕ) : ℤ) = sg.w i - sg.w ⟨n - 1, by have := i.2; omega⟩ := by
  have hle : i ≤ ⟨n - 1, by have := i.2; omega⟩ := by rw [Fin.le_def]; simp; have := i.2; omega
  have := sg.anti hle
  simp only [DomWeight.natW, DomWeight.detShift, dif_pos (show 0 < n by have := i.2; omega)]
  rw [Int.toNat_of_nonneg (by omega)]

theorem card_lt_sz {n K : ℕ} (sg : DomWeight n) (sz : Fin K → ℕ) (hshape : shapeDeg sz = sg.natW)
    (t : Fin n) : (Finset.univ.filter fun k => t.1 < sz k).card = sg.natW t := by
  rw [← hshape]; rfl

theorem sz_lt {n K : ℕ} (sg : DomWeight n) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (hshape : shapeDeg sz = sg.natW) (k : Fin K) : sz k < n ∨ sz k = 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · right; have := hsz k; omega
  · left
    have h1 := card_lt_sz sg sz hshape ⟨n - 1, by omega⟩
    have h0 : sg.natW ⟨n - 1, by omega⟩ = 0 := by
      simp [DomWeight.natW, DomWeight.detShift, dif_pos hn]
    rw [h0, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h1
    have hk := h1 (Finset.mem_univ k)
    simp only [not_lt] at hk
    have := hsz k
    omega

theorem card_eq_sz {n K : ℕ} (sg : DomWeight n) (sz : Fin K → ℕ) (hshape : shapeDeg sz = sg.natW)
    (i : ℕ) (hi : i + 1 < n) :
    (Finset.univ.filter fun k => sz k = i + 1).card = sg.natW ⟨i, by omega⟩ - sg.natW ⟨i + 1, hi⟩ := by
  have h1 := card_lt_sz sg sz hshape ⟨i, by omega⟩
  have h2 := card_lt_sz sg sz hshape ⟨i + 1, hi⟩
  simp only at h1 h2
  rw [← h1, ← h2]
  have : (Finset.univ.filter fun k => i < sz k) =
      (Finset.univ.filter fun k => i + 1 < sz k) ∪ (Finset.univ.filter fun k => sz k = i + 1) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]; omega
  rw [this, Finset.card_union_of_disjoint]
  · omega
  · rw [Finset.disjoint_filter]; intro k _ h1 h2; omega

theorem goodL_exists {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    {K : ℕ} (sz : Fin K → ℕ) (hshape : shapeDeg sz = sg.natW) :
    ∃ L : Finset (Fin K), GoodL h lam sg sz L := by
  classical
  have hB : ∀ i : Fin n, (if i.1 = 0 then 0 else (bb h lam sg i).toNat) ≤
      (Finset.univ.filter fun k => sz k = i.1).card := by
    intro i
    split_ifs with hi0
    · exact Nat.zero_le _
    · obtain ⟨iv, hiv⟩ := i
      obtain ⟨j, rfl⟩ : ∃ j, iv = j + 1 := ⟨iv - 1, by simp at hi0; omega⟩
      have hc := card_eq_sz sg sz hshape j hiv
      simp only at hc ⊢
      rw [hc]
      have e1 := natW_sg_val sg ⟨j, by omega⟩
      have e2 := natW_sg_val sg ⟨j + 1, hiv⟩
      have hb := (hI ⟨j + 1, hiv⟩).1
      have ha := (hI ⟨j, by omega⟩).2
      unfold bb
      simp only at hb ha e1 e2 ⊢
      omega
  choose T hT using fun i : Fin n => Finset.exists_subset_card_eq (hB i)
  refine ⟨Finset.univ.biUnion T, ?_, ?_⟩
  · intro k hk
    obtain ⟨i, _, hki⟩ := Finset.mem_biUnion.mp hk
    have hs := (hT i).1 hki
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    by_cases hi0 : i.1 = 0
    · have hc := (hT i).2
      rw [if_pos hi0, Finset.card_eq_zero] at hc
      rw [hc] at hki; exact absurd hki (Finset.notMem_empty k)
    · omega
  · intro i
    rw [← (hT i).2]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨j, hkj⟩, hsk⟩
      have hs := (hT j).1 hkj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      have : j = i := Fin.ext (by omega)
      subst this; exact hkj
    · intro hki
      have hs := (hT i).1 hki
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      exact ⟨⟨i, hki⟩, hs⟩

end PI.WGL.LTD
