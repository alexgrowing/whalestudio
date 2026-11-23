import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm

noncomputable section

namespace GlobalTheory.PMonE.LinCount

open Finset GlobalTheory.PMonE

variable {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]

def lin (K : ℕ) (M : ℕ → Matrix m m F) (k : ℕ) : Matrix (Fin (K + 1) × m) (Fin (K + 1) × m) F :=
  fun r c =>
    if r.1 = Fin.last K then
      (if k = 0 then M c.1 r.2 c.2 else if c.1 = Fin.last K then M (k + K) r.2 c.2 else 0)
    else
      (if k = 0 then (if (c.1 : ℕ) = r.1 + 1 ∧ r.2 = c.2 then -1 else 0)
        else if k = 1 then (if r = c then 1 else 0) else 0)

theorem lin_normal (K : ℕ) (M : ℕ → Matrix m m F) (h : Normal (K + 1) M) : Normal 1 (lin K M) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n r c
    unfold lin
    split_ifs <;> first | exact h.int _ _ _ | simp
  · ext ⟨i, a⟩ ⟨j, b⟩
    have h1 : M (1 + K) = 1 := by rw [add_comm]; exact h.top
    by_cases hi : i = Fin.last K
    · subst hi
      by_cases hj : j = Fin.last K
      · subst hj
        simp [lin, h1, Matrix.one_apply]
      · simp [lin, hj, Matrix.one_apply, Ne.symm hj]
    · simp [lin, hi, Matrix.one_apply]
  · intro n hn r c
    have h0 : n ≠ 0 := by omega
    have h1 : n ≠ 1 := by omega
    simp only [lin, h0, h1, if_false]
    split_ifs
    · exact h.small _ (by omega) _ _
    · simp
    · simp

theorem lin_zero_cast (K : ℕ) (M : ℕ → Matrix m m F) (Y : Fin (K + 1) × m → F) (i : Fin K) (a : m) :
    (lin K M 0).mulVec Y (i.castSucc, a) = - Y (i.succ, a) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (i.succ, a)]
  · simp [lin, (Fin.castSucc_lt_last i).ne]
  · rintro ⟨j, b⟩ _ hne
    have : ¬ ((j : ℕ) = i + 1 ∧ a = b) := by
      rintro ⟨h1, rfl⟩
      exact hne (by congr 1; exact Fin.ext (by simpa using h1))
    simp [lin, (Fin.castSucc_lt_last i).ne, this]
  · simp

theorem lin_one_cast (K : ℕ) (M : ℕ → Matrix m m F) (Y : Fin (K + 1) × m → F) (i : Fin K) (a : m) :
    (lin K M 1).mulVec Y (i.castSucc, a) = Y (i.castSucc, a) := by
  simp [Matrix.mulVec, dotProduct, lin, (Fin.castSucc_lt_last i).ne]

theorem lin_two_cast (K : ℕ) (M : ℕ → Matrix m m F) (k : ℕ) (Y : Fin (K + 1) × m → F) (i : Fin K) (a : m) :
    (lin K M (k + 1 + 1)).mulVec Y (i.castSucc, a) = 0 := by
  simp [Matrix.mulVec, dotProduct, lin, (Fin.castSucc_lt_last i).ne]

theorem lin_zero_last (K : ℕ) (M : ℕ → Matrix m m F) (Y : Fin (K + 1) × m → F) (a : m) :
    (lin K M 0).mulVec Y (Fin.last K, a) = ∑ j : Fin (K + 1), (M j).mulVec (fun b => Y (j, b)) a := by
  simp [Matrix.mulVec, dotProduct, lin, Fintype.sum_prod_type]

theorem lin_succ_last (K : ℕ) (M : ℕ → Matrix m m F) (k : ℕ) (Y : Fin (K + 1) × m → F) (a : m) :
    (lin K M (k + 1)).mulVec Y (Fin.last K, a) = (M (k + 1 + K)).mulVec (fun b => Y (Fin.last K, b)) a := by
  simp only [Matrix.mulVec, dotProduct, lin, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (Fin.last K)]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem lin_det (K : ℕ) (M : ℕ → Matrix m m F) (h : (M 0).det ≠ 0) : (lin K M 0).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hs : ∀ (i : Fin K) (a : m), v (i.succ, a) = 0 := by
    intro i a
    have := congrFun hv0 (i.castSucc, a)
    rw [lin_zero_cast] at this
    simpa using this
  have hz : (M 0).mulVec (fun b => v (0, b)) = 0 := by
    funext a
    have := congrFun hv0 (Fin.last K, a)
    rw [lin_zero_last, Fin.sum_univ_succ] at this
    simpa [hs, Matrix.mulVec, dotProduct] using this
  have h00 : (fun b => v (0, b)) = 0 := by
    by_contra hne
    exact h (Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hne, hz⟩)
  apply hv
  funext ⟨j, b⟩
  refine Fin.cases ?_ (fun i => ?_) j
  · exact congrFun h00 b
  · exact hs i b

theorem gsum_lin_cast (q K E : ℕ) (M : ℕ → Matrix m m F) (X : Fin (K + 1) × m → F) (i : Fin K) (a : m) :
    gsum q (E + 1) (lin K M) X (i.castSucc, a) = X (i.castSucc, a) ^ q - X (i.succ, a) := by
  simp only [gsum, Finset.sum_apply]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [lin_two_cast, zero_add, lin_one_cast, lin_zero_cast]
  simp [sub_eq_add_neg]

theorem gsum_lin_last (q K E : ℕ) (M : ℕ → Matrix m m F) (x : m → F) (a : m) :
    gsum q E (lin K M) (fun r => x r.2 ^ q ^ (r.1 : ℕ)) (Fin.last K, a) = gsum q (K + E) M x a := by
  simp only [gsum, Finset.sum_apply]
  rw [Finset.sum_range_succ', show K + E + 1 = (K + 1) + E by ring, Finset.sum_range_add, add_comm]
  congr 1
  · rw [lin_zero_last, Finset.sum_range]
    simp
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [lin_succ_last, show k + 1 + K = K + 1 + k by ring]
    congr 1
    funext b
    simp only [Fin.val_last]
    rw [← pow_mul, ← pow_add, show K + (k + 1) = K + 1 + k by ring]

theorem card_lin (q K E : ℕ) (M : ℕ → Matrix m m F) :
    Nat.card {x : m → F // Integral x ∧ gsum q (K + (E + 1)) M x = 0} =
      Nat.card {X : Fin (K + 1) × m → F // Integral X ∧ gsum q (E + 1) (lin K M) X = 0} := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => ⟨fun r => x.1 r.2 ^ q ^ (r.1 : ℕ), ?_, ?_⟩) ⟨?_, ?_⟩)
  · intro r
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (x.2.1 _)
  · funext ⟨j, a⟩
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [gsum_lin_last, x.2.2]; rfl
    · rw [gsum_lin_cast]
      simp [pow_succ, pow_mul]
  · intro x y hxy
    ext a
    have := congrFun (congrArg Subtype.val hxy) (0, a)
    simpa using this
  · rintro ⟨X, hX, hX0⟩
    have key : X = fun r => X (0, r.2) ^ q ^ (r.1 : ℕ) := by
      funext ⟨j, a⟩
      induction j using Fin.induction with
      | zero => simp
      | succ i ih =>
        have := congrFun hX0 (i.castSucc, a)
        rw [gsum_lin_cast, Pi.zero_apply, sub_eq_zero] at this
        rw [← this, ih]
        simp [pow_succ, pow_mul]
    refine ⟨⟨fun a => X (0, a), fun a => hX _, ?_⟩, Subtype.ext key.symm⟩
    funext a
    rw [← gsum_lin_last, ← key, hX0]; rfl

theorem glCount_of_one : ∀ N : ℕ, 1 ≤ N → GLCount 1 → GLCount N := by
  intro N hN h1 F _ _ _ _ p _ _ m _ _ e D he hD M hM hdet
  obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
  obtain ⟨E, rfl⟩ : ∃ E, D = K + (E + 1) := ⟨D - K - 1, by omega⟩
  rw [card_lin, h1 F p (Fin (K + 1) × m) e (E + 1) he (by omega) (lin K M) (lin_normal K M hM) (lin_det K M hdet)]
  simp [mul_comm]

end GlobalTheory.PMonE.LinCount

end
