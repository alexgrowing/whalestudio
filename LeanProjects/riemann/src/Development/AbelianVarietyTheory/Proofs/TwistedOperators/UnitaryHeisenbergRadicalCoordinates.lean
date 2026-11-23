import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta.HeisCoord

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

def Shape (M : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (r b : Fin N → L) (c : L) : Prop :=
  M 0 0 = 1 ∧ (∀ j, M 0 (mid j) = r j) ∧ M 0 (Fin.last (N + 1)) = c ∧ (∀ i, M (mid i) 0 = 0) ∧
  (∀ i j, M (mid i) (mid j) = if i = j then 1 else 0) ∧ (∀ i, M (mid i) (Fin.last (N + 1)) = b i) ∧
  M (Fin.last (N + 1)) 0 = 0 ∧ (∀ j, M (Fin.last (N + 1)) (mid j) = 0) ∧
  M (Fin.last (N + 1)) (Fin.last (N + 1)) = 1

theorem form_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (cT σ M * antiJ L n * M) i j = ∑ l, σ (M l.rev i) * M l j := by
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun l _ => by rw [P.fSatake_cTJ]

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem antiJ_eq {n : ℕ} (a b : Fin n) : antiJ L n a b = if a = b.rev then 1 else 0 := by
  simp only [antiJ, P.fSatake_rev_iff]

theorem shape_of_mem {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) : Shape (mat u) (rowOf u) (colOf u) (cornerOf u) := by
  have h : ∀ i j, blk N j ≤ blk N i → mat u i j = (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i j := hu
  refine ⟨?_, fun j => rfl, rfl, fun i => ?_, fun i j => ?_, fun i => rfl, ?_, fun j => ?_, ?_⟩
  · rw [h 0 0 le_rfl, Matrix.one_apply_eq]
  · rw [h _ _ (by simp), Matrix.one_apply_ne (mid_ne_zero i)]
  · rw [h _ _ (by simp)]; simp [Matrix.one_apply, mid_injective.eq_iff]
  · rw [h _ _ (by simp), Matrix.one_apply_ne last_ne_zero]
  · rw [h _ _ (by simp), Matrix.one_apply_ne (mid_ne_last j).symm]
  · rw [h _ _ le_rfl, Matrix.one_apply_eq]

theorem sum_rev_ite {M : Type} [AddCommMonoid M] (f : Fin N → M) (j : Fin N) :
    (∑ x, if x.rev = j then f x else 0) = f j.rev := by
  rw [Finset.sum_eq_single j.rev]
  · simp
  · intro x _ hx
    rw [if_neg fun e => hx (by rw [← e, Fin.rev_rev])]
  · simp

theorem form_mid_last {M : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {r b : Fin N → L} {c : L} (h : Shape M r b c)
    (j : Fin N) : (cT σ M * antiJ L (N + 2) * M) (mid j) (Fin.last (N + 1)) = b j.rev + σ (r j) := by
  obtain ⟨h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll⟩ := h
  rw [form_apply, sum_idx]
  simp [Fin.rev_zero, Fin.rev_last, ← mid_rev, h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll, sum_rev_ite]

theorem form_last_last {M : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {r b : Fin N → L} {c : L} (h : Shape M r b c) :
    (cT σ M * antiJ L (N + 2) * M) (Fin.last (N + 1)) (Fin.last (N + 1)) = c + ∑ k, σ (b k.rev) * b k + σ c := by
  obtain ⟨h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll⟩ := h
  rw [form_apply, sum_idx]
  simp [Fin.rev_zero, Fin.rev_last, ← mid_rev, h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll, sum_rev_ite]

theorem zero_ne_mid (i : Fin N) : (0 : Fin (N + 2)) ≠ mid i := (mid_ne_zero i).symm
theorem last_ne_mid (i : Fin N) : Fin.last (N + 1) ≠ mid i := (mid_ne_last i).symm

theorem form_eq_of (hσσ : ∀ x, σ (σ x) = x) {M : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {r b : Fin N → L} {c : L}
    (h : Shape M r b c) (h1 : ∀ j, b j.rev + σ (r j) = 0) (h2 : c + ∑ k, σ (b k.rev) * b k + σ c = 0) :
    cT σ M * antiJ L (N + 2) * M = antiJ L (N + 2) := by
  obtain ⟨h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll⟩ := h
  ext i j
  rw [form_apply, sum_idx, antiJ_eq]
  rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl <;>
    simp [Fin.rev_zero, Fin.rev_last, ← mid_rev, h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll, sum_rev_ite,
      mid_ne_zero, mid_ne_last, zero_ne_mid, last_ne_mid, mid_injective.eq_iff]
  · by_cases e : i = j.rev
    · subst e; simp
    · rw [if_neg e, if_neg fun e' => e e'.symm]
  · exact h1 i
  · have := congrArg σ (h1 j)
    simp only [map_add, hσσ, map_zero] at this
    linear_combination this
  · exact h2

def heisMat (r b : Fin N → L) (c : L) : Matrix (Fin (N + 2)) (Fin (N + 2)) L := fun i j =>
  if i = j then 1
  else if i = 0 ∧ j = Fin.last (N + 1) then c
  else if h : i = 0 ∧ 0 < j.val ∧ j.val < N + 1 then r ⟨j.val - 1, by omega⟩
  else if h : j = Fin.last (N + 1) ∧ 0 < i.val ∧ i.val < N + 1 then b ⟨i.val - 1, by omega⟩
  else 0

theorem shape_heisMat (r b : Fin N → L) (c : L) : Shape (heisMat r b c) r b c := by
  refine ⟨by simp [heisMat], fun j => ?_, by simp [heisMat, last_ne_zero.symm], fun i => ?_, fun i j => ?_,
    fun i => ?_, by simp [heisMat, last_ne_zero], fun j => ?_, by simp [heisMat]⟩
  · have := j.2
    simp [heisMat, zero_ne_mid, mid_ne_last]
  · simp [heisMat, mid_ne_zero, last_ne_zero.symm]
  · simp [heisMat, mid_injective.eq_iff, mid_ne_zero, mid_ne_last]
  · have := i.2
    simp [heisMat, mid_ne_zero, mid_ne_last]
  · simp [heisMat, last_ne_mid, last_ne_zero]

theorem mem_radQ_of_shape {u : GU σ (N + 2)} {r b : Fin N → L} {c : L} (h : Shape (mat u) r b c) :
    u ∈ radQ σ N := by
  obtain ⟨h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll⟩ := h
  intro i j hij
  rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl <;>
    simp [Matrix.one_apply, h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll, mid_ne_zero, mid_ne_last, zero_ne_mid,
      last_ne_mid, mid_injective.eq_iff] at hij ⊢

theorem mul_coords {u u' : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hu' : u' ∈ radQ σ N) :
    rowOf (u * u') = rowOf u + rowOf u' ∧ colOf (u * u') = colOf u + colOf u' ∧
      cornerOf (u * u') = cornerOf u + cornerOf u' + rowOf u ⬝ᵥ colOf u' := by
  obtain ⟨h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll⟩ := shape_of_mem hu
  obtain ⟨h00', h0m', h0l', hm0', hmm', hml', hl0', hlm', hll'⟩ := shape_of_mem hu'
  refine ⟨funext fun j => ?_, funext fun i => ?_, ?_⟩
  · simp only [rowOf, mat_mul, Matrix.mul_apply, sum_idx, Pi.add_apply]
    simp [h00, h0m, h0l, hmm', hl0', hlm', h0m']
    ring
  · simp only [colOf, mat_mul, Matrix.mul_apply, sum_idx, Pi.add_apply]
    simp [hm0, hmm, hml, hml', hll', h0l']
    ring
  · simp only [cornerOf, mat_mul, Matrix.mul_apply, sum_idx, dotProduct]
    simp [h00, h0m, h0l, hml', hll', h0l']
    ring

theorem Heisenberg₂ : Heis := by
  intro L _ _ ϖ σ q N hU
  obtain ⟨hσσ, hv, -⟩ := hU
  have hσint : ∀ x, x ∈ intL L → σ x ∈ intL L := fun x hx => by
    show Valued.v (σ x) ≤ 1
    rw [hv]; exact hx
  refine ⟨fun u hu => ?_, fun u hu u' hu' => mul_coords hu hu', fun r c hc => ?_⟩
  · have hs := shape_of_mem hu
    have hf : cT σ (mat u) * antiJ L (N + 2) * mat u = antiJ L (N + 2) := u.2
    have h1 : ∀ j, colOf u j.rev + σ (rowOf u j) = 0 := fun j => by
      have := congrFun (congrFun hf (mid j)) (Fin.last (N + 1))
      rwa [form_mid_last hs, antiJ_eq, if_neg (by rw [Fin.rev_last]; exact mid_ne_zero j)] at this
    have h2 : cornerOf u + ∑ k, σ (colOf u k.rev) * colOf u k + σ (cornerOf u) = 0 := by
      have := congrFun (congrFun hf (Fin.last (N + 1))) (Fin.last (N + 1))
      rwa [form_last_last hs, antiJ_eq, if_neg (by rw [Fin.rev_last]; exact last_ne_zero)] at this
    have hr : ∀ j, rowOf u j = -σ (colOf u j.rev) := fun j => by
      have := congrArg σ (h1 j)
      simp only [map_add, hσσ, map_zero] at this
      linear_combination this
    refine ⟨hr, ?_, ?_⟩
    · simp only [dotProduct, hr, neg_mul, Finset.sum_neg_distrib]
      linear_combination h2
    · rw [mem_KU_iff hv]
      constructor
      · intro h
        exact ⟨fun j => h _ _, h _ _⟩
      · rintro ⟨hr', hc'⟩ i j
        obtain ⟨h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll⟩ := hs
        have hb : ∀ i, colOf u i ∈ intL L := fun i => by
          have e := hr i.rev
          rw [Fin.rev_rev] at e
          have h' : colOf u i = -σ (rowOf u i.rev) := by rw [e, map_neg, hσσ, neg_neg]
          rw [h']
          exact neg_mem (hσint _ (hr' _))
        rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl <;>
          simp only [h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll] <;>
          first | exact one_mem _ | exact zero_mem _ | exact hr' _ | exact hc' | exact hb _ |
            (split_ifs <;> first | exact one_mem _ | exact zero_mem _)
  · let b : Fin N → L := fun i => -σ (r i.rev)
    have h1 : ∀ j, b j.rev + σ (r j) = 0 := fun j => by simp [b]
    have h2 : c + ∑ k, σ (b k.rev) * b k + σ c = 0 := by
      simp only [b, Fin.rev_rev, map_neg, hσσ, neg_mul_neg]
      linear_combination hc
    obtain ⟨g, hg⟩ := exists_mat (σ := σ) (heisMat r b c) (form_eq_of hσσ (shape_heisMat r b c) h1 h2)
    have hs : Shape (mat g) r b c := hg ▸ shape_heisMat r b c
    exact ⟨g, mem_radQ_of_shape hs, funext hs.2.1, hs.2.2.1⟩

end GlobalTheory.InertZeta.HeisCoord
