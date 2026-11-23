import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstKernelExplicitFormula
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModulusLocallyConstant

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism.FourierDecayAlt.P.A5x8 (sec_m sec_m_ext sec_gl sec_gl_coe sec_fib sec_right_eq sec_left_eq sec_mem_int toCos)

noncomputable section

namespace Formalism.FourierDecayAlt.P.TwoBlockPoint

section GlobalTheory
variable {K : Type} [CommRing K] {a s N : ℕ}

def eN (hN : N = a + s) : Fin a ⊕ Fin s ≃ Fin N := finSumFinEquiv.trans (finCongr hN.symm)

theorem eN_inl (hN : N = a + s) (i : Fin a) : ((eN hN (Sum.inl i) : Fin N) : ℕ) = i := by
  first
    | simp [eN]
    | rfl

theorem eN_inr (hN : N = a + s) (i : Fin s) : ((eN hN (Sum.inr i) : Fin N) : ℕ) = a + i := by
  first
    | simp [eN]
    | rfl

def blkM (hN : N = a + s) (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin a) (Fin s) K)
    (C : Matrix (Fin s) (Fin a) K) (D : Matrix (Fin s) (Fin s) K) : Matrix (Fin N) (Fin N) K :=
  (fromBlocks A B C D).submatrix (eN hN).symm (eN hN).symm

variable (hN : N = a + s) (A A' : Matrix (Fin a) (Fin a) K) (B B' : Matrix (Fin a) (Fin s) K)
    (C C' : Matrix (Fin s) (Fin a) K) (D D' : Matrix (Fin s) (Fin s) K)

theorem blkM_ll (i j : Fin a) : blkM hN A B C D (eN hN (Sum.inl i)) (eN hN (Sum.inl j)) = A i j := by
  simp [blkM]

theorem blkM_lr (i : Fin a) (j : Fin s) :
    blkM hN A B C D (eN hN (Sum.inl i)) (eN hN (Sum.inr j)) = B i j := by
  simp [blkM]

theorem blkM_rl (i : Fin s) (j : Fin a) :
    blkM hN A B C D (eN hN (Sum.inr i)) (eN hN (Sum.inl j)) = C i j := by
  simp [blkM]

theorem blkM_rr (i j : Fin s) : blkM hN A B C D (eN hN (Sum.inr i)) (eN hN (Sum.inr j)) = D i j := by
  simp [blkM]

theorem eq_blkM (M : Matrix (Fin N) (Fin N) K) :
    M = blkM hN (Matrix.of fun i j => M (eN hN (Sum.inl i)) (eN hN (Sum.inl j)))
      (Matrix.of fun i j => M (eN hN (Sum.inl i)) (eN hN (Sum.inr j)))
      (Matrix.of fun i j => M (eN hN (Sum.inr i)) (eN hN (Sum.inl j)))
      (Matrix.of fun i j => M (eN hN (Sum.inr i)) (eN hN (Sum.inr j))) := by
  ext x y
  obtain ⟨p, rfl⟩ := (eN hN).surjective x
  obtain ⟨q, rfl⟩ := (eN hN).surjective y
  rcases p with p | p <;> rcases q with q | q <;> simp [blkM]

variable {A A' B B' C C' D D'} in
theorem blkM_inj (h : blkM hN A B C D = blkM hN A' B' C' D') :
    A = A' ∧ B = B' ∧ C = C' ∧ D = D' := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j
  · simpa [blkM] using congrFun (congrFun h (eN hN (Sum.inl i))) (eN hN (Sum.inl j))
  · simpa [blkM] using congrFun (congrFun h (eN hN (Sum.inl i))) (eN hN (Sum.inr j))
  · simpa [blkM] using congrFun (congrFun h (eN hN (Sum.inr i))) (eN hN (Sum.inl j))
  · simpa [blkM] using congrFun (congrFun h (eN hN (Sum.inr i))) (eN hN (Sum.inr j))

theorem blkM_mul : blkM hN A B C D * blkM hN A' B' C' D' =
    blkM hN (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  unfold blkM
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blkM_add : blkM hN A B C D + blkM hN A' B' C' D' =
    blkM hN (A + A') (B + B') (C + C') (D + D') := by
  ext x y
  obtain ⟨p, rfl⟩ := (eN hN).surjective x
  obtain ⟨q, rfl⟩ := (eN hN).surjective y
  rcases p with p | p <;> rcases q with q | q <;> simp [blkM]

theorem blkM_one : blkM hN (1 : Matrix (Fin a) (Fin a) K) 0 0 1 = 1 := by
  unfold blkM
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem blkM_det_low : (blkM hN A 0 C D).det = A.det * D.det := by
  unfold blkM
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂]

theorem blkM_det_up : (blkM hN A B 0 D).det = A.det * D.det := by
  unfold blkM
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]

theorem blkM_isInt (R : Subring K) : IsInt R (blkM hN A B C D) ↔
      IsInt R A ∧ (∀ i j, B i j ∈ R) ∧ (∀ i j, C i j ∈ R) ∧ IsInt R D := by
  unfold IsInt
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · simpa [blkM] using h (eN hN (Sum.inl i)) (eN hN (Sum.inl j))
    · simpa [blkM] using h (eN hN (Sum.inl i)) (eN hN (Sum.inr j))
    · simpa [blkM] using h (eN hN (Sum.inr i)) (eN hN (Sum.inl j))
    · simpa [blkM] using h (eN hN (Sum.inr i)) (eN hN (Sum.inr j))
  · rintro ⟨h1, h2, h3, h4⟩ x y
    obtain ⟨p, rfl⟩ := (eN hN).surjective x
    obtain ⟨q, rfl⟩ := (eN hN).surjective y
    rcases p with p | p <;> rcases q with q | q <;> simp [blkM, h1, h2, h3, h4]

theorem eN_ll_lt (i j : Fin a) : eN hN (Sum.inl i) < eN hN (Sum.inl j) ↔ i < j := by
  rw [Fin.lt_iff_val_lt_val, Fin.lt_iff_val_lt_val, eN_inl, eN_inl]

theorem eN_rr_lt (i j : Fin s) : eN hN (Sum.inr i) < eN hN (Sum.inr j) ↔ i < j := by
  rw [Fin.lt_iff_val_lt_val, Fin.lt_iff_val_lt_val, eN_inr, eN_inr]
  omega

theorem eN_lr_lt (i : Fin a) (j : Fin s) : eN hN (Sum.inl i) < eN hN (Sum.inr j) := by
  rw [Fin.lt_iff_val_lt_val, eN_inl, eN_inr]
  have := i.isLt
  omega

private lemma lowTri_lemma {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    M.IsLowerTriangular ↔ ∀ i j, i < j → M i j = 0 :=
  ⟨fun h i j hij => h hij, fun h i j hij => h i j hij⟩

theorem blkM_isLowUni : IsLowUni (blkM hN A B C D) ↔ IsLowUni A ∧ B = 0 ∧ IsLowUni D := by
  simp only [IsLowUni, lowTri_lemma]
  constructor
  · rintro ⟨hL, hD⟩
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, ?_, fun i j hij => ?_, fun i => ?_⟩
    · simpa [blkM_ll] using hL _ _ ((eN_ll_lt hN i j).2 hij)
    · simpa [blkM_ll] using hD (eN hN (Sum.inl i))
    · ext i j
      simpa [blkM_lr] using hL _ _ (eN_lr_lt hN i j)
    · simpa [blkM_rr] using hL _ _ ((eN_rr_lt hN i j).2 hij)
    · simpa [blkM_rr] using hD (eN hN (Sum.inr i))
  · rintro ⟨⟨hA, hA1⟩, rfl, hD, hD1⟩
    refine ⟨fun x y hxy => ?_, fun x => ?_⟩
    · obtain ⟨p, rfl⟩ := (eN hN).surjective x
      obtain ⟨q, rfl⟩ := (eN hN).surjective y
      rcases p with i | i <;> rcases q with j | j
      · rw [blkM_ll]
        exact hA i j ((eN_ll_lt hN i j).1 hxy)
      · simp [blkM_lr]
      · exact absurd hxy (not_lt.2 (eN_lr_lt hN j i).le)
      · rw [blkM_rr]
        exact hD i j ((eN_rr_lt hN i j).1 hxy)
    · obtain ⟨p, rfl⟩ := (eN hN).surjective x
      rcases p with i | i
      · rw [blkM_ll]
        exact hA1 i
      · rw [blkM_rr]
        exact hD1 i

private lemma upTri_lemma {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    M.IsUpperTriangular ↔ ∀ i j, j < i → M i j = 0 :=
  ⟨fun h i j hij => h hij, fun h i j hij => h i j hij⟩

theorem blkM_isUpUni : IsUpUni (blkM hN A B C D) ↔ IsUpUni A ∧ C = 0 ∧ IsUpUni D := by
  simp only [IsUpUni, upTri_lemma]
  constructor
  · rintro ⟨hL, hD⟩
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, ?_, fun i j hij => ?_, fun i => ?_⟩
    · simpa [blkM_ll] using hL _ _ ((eN_ll_lt hN j i).2 hij)
    · simpa [blkM_ll] using hD (eN hN (Sum.inl i))
    · ext i j
      simpa [blkM_rl] using hL _ _ (eN_lr_lt hN j i)
    · simpa [blkM_rr] using hL _ _ ((eN_rr_lt hN j i).2 hij)
    · simpa [blkM_rr] using hD (eN hN (Sum.inr i))
  · rintro ⟨⟨hA, hA1⟩, rfl, hD, hD1⟩
    refine ⟨fun x y hxy => ?_, fun x => ?_⟩
    · obtain ⟨p, rfl⟩ := (eN hN).surjective x
      obtain ⟨q, rfl⟩ := (eN hN).surjective y
      rcases p with i | i <;> rcases q with j | j
      · rw [blkM_ll]
        exact hA i j ((eN_ll_lt hN j i).1 hxy)
      · exact absurd hxy (not_lt.2 (eN_lr_lt hN i j).le)
      · simp [blkM_rl]
      · rw [blkM_rr]
        exact hD i j ((eN_rr_lt hN j i).1 hxy)
    · obtain ⟨p, rfl⟩ := (eN hN).surjective x
      rcases p with i | i
      · rw [blkM_ll]
        exact hA1 i
      · rw [blkM_rr]
        exact hD1 i

def cornL (C : Matrix (Fin s) (Fin a) K) : K :=
  ∑ j : Fin a, ∑ i : Fin s, if i.val = 0 ∧ j.val + 1 = a then C i j else 0

def cornU (B : Matrix (Fin a) (Fin s) K) : K :=
  ∑ i : Fin a, ∑ j : Fin s, if j.val = 0 ∧ i.val + 1 = a then B i j else 0

def bigZ (hN : N = a + s) (Z : Matrix (Fin a) (Fin a) K) (X : Matrix (Fin s) (Fin a) K)
    (Y : Matrix (Fin a) (Fin s) K) (G : Matrix (Fin s) (Fin s) K) : Matrix (Fin N) (Fin N) K :=
  blkM hN Z (Z * Y) (X * Z) (X * Z * Y + G)

end GlobalTheory

section Phi
variable {K : Type} [CommRing K] (R : Subring K)

open Classical in

def Fz {n n' : ℕ} (Z' : Matrix (Fin n') (Fin n') K) (Z : Matrix (Fin n) (Fin n) K) : ℂ :=
  if IsInt R Z then (Nat.card (isoZZ R Z Z') : ℂ) else 0

def outM {ι κ : Type} (x : Matrix ι κ (KR R)) : Matrix ι κ K := fun i j => Quotient.out (x i j)

def clsM {ι κ : Type} (x : Matrix ι κ K) : Matrix ι κ (KR R) :=
  fun i j => Submodule.Quotient.mk (x i j)

def PhiH (ψ : AddChar K ℂ) (h : Point K) {n' : ℕ} (Z' : Matrix (Fin n') (Fin n') K) (n : ℕ)
    (G : Matrix (Fin n) (Fin n) K) : ℂ :=
  ∑ᶠ τ : Cos R h × Matrix (Fin n) (Fin h.1.sum) (KR R) × Matrix (Fin h.1.sum) (Fin n) (KR R),
    Fz R Z' (bigZ rfl (orbZ h (rep R τ.1)) (outM R τ.2.1) (outM R τ.2.2) G) *
      (phase ψ (rep R τ.1) * ψ (cornL (outM R τ.2.1) + cornU (outM R τ.2.2)))

end Phi

section Simple
variable {K : Type} [CommRing K] {a s N : ℕ}

private lemma sLow_lemma {n : ℕ} (x : Matrix (Fin n) (Fin n) K) :
    sLow x = ∑ j : Fin n, ∑ i : Fin n, if (i : ℕ) = j + 1 then x i j else 0 := by
  unfold sLow
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j + 1, h⟩]
    · simp
    · intro i _ hi
      rw [if_neg]
      intro e
      exact hi (Fin.ext e)
    · simp
  · symm
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro e
    have := i.2
    omega

theorem sLow_blkM (hN : N = a + s) (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin a) (Fin s) K)
    (C : Matrix (Fin s) (Fin a) K) (D : Matrix (Fin s) (Fin s) K) :
    sLow (blkM hN A B C D) = sLow A + sLow D + cornL C := by
  rw [sLow_lemma, sLow_lemma, sLow_lemma]
  simp only [← (eN hN).sum_comp, Fintype.sum_sum_type, eN_inl, eN_inr, blkM_ll, blkM_lr, blkM_rl,
    blkM_rr, Finset.sum_add_distrib]
  have hB : ∀ (j : Fin s) (i : Fin a), (if (i : ℕ) = a + j + 1 then B i j else 0) = 0 := by
    intro j i
    have := i.2
    rw [if_neg (by omega)]
  have hC : ∀ (j : Fin a) (i : Fin s),
      (if a + (i : ℕ) = j + 1 then C i j else 0) = (if (i : ℕ) = 0 ∧ (j : ℕ) + 1 = a then C i j else 0) := by
    intro j i
    have := j.2
    simp only [show (a + (i : ℕ) = j + 1) ↔ ((i : ℕ) = 0 ∧ (j : ℕ) + 1 = a) by omega]
  have hD : ∀ (j i : Fin s),
      (if a + (i : ℕ) = a + j + 1 then D i j else 0) = (if (i : ℕ) = j + 1 then D i j else 0) := by
    intro j i
    simp only [show (a + (i : ℕ) = a + j + 1) ↔ ((i : ℕ) = j + 1) by omega]
  simp only [hB, hC, hD, Finset.sum_const_zero, add_zero, zero_add]
  unfold cornL
  abel

private lemma sUp_lemma {n : ℕ} (x : Matrix (Fin n) (Fin n) K) :
    sUp x = ∑ j : Fin n, ∑ i : Fin n, if (i : ℕ) = j + 1 then x j i else 0 := by
  unfold sUp
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j + 1, h⟩]
    · simp
    · intro i _ hi
      rw [if_neg]
      intro e
      exact hi (Fin.ext e)
    · simp
  · symm
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro e
    have := i.2
    omega

theorem sUp_blkM (hN : N = a + s) (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin a) (Fin s) K)
    (C : Matrix (Fin s) (Fin a) K) (D : Matrix (Fin s) (Fin s) K) :
    sUp (blkM hN A B C D) = sUp A + sUp D + cornU B := by
  rw [sUp_lemma, sUp_lemma, sUp_lemma]
  simp only [← (eN hN).sum_comp, Fintype.sum_sum_type, eN_inl, eN_inr, blkM_ll, blkM_lr, blkM_rl,
    blkM_rr, Finset.sum_add_distrib]
  have hC : ∀ (j : Fin s) (i : Fin a), (if (i : ℕ) = a + j + 1 then C j i else 0) = 0 := by
    intro j i
    have := i.2
    rw [if_neg (by omega)]
  have hB : ∀ (j : Fin a) (i : Fin s),
      (if a + (i : ℕ) = j + 1 then B j i else 0) = (if (i : ℕ) = 0 ∧ (j : ℕ) + 1 = a then B j i else 0) := by
    intro j i
    have := j.2
    simp only [show (a + (i : ℕ) = j + 1) ↔ ((i : ℕ) = 0 ∧ (j : ℕ) + 1 = a) by omega]
  have hD : ∀ (j i : Fin s),
      (if a + (i : ℕ) = a + j + 1 then D j i else 0) = (if (i : ℕ) = j + 1 then D j i else 0) := by
    intro j i
    simp only [show (a + (i : ℕ) = a + j + 1) ↔ ((i : ℕ) = j + 1) by omega]
  simp only [hB, hC, hD, Finset.sum_const_zero, add_zero, zero_add]
  unfold cornU
  abel

theorem cornL_mul_low {v : Matrix (Fin a) (Fin a) K} (hv : IsLowUni v)
    (X : Matrix (Fin s) (Fin a) K) : cornL (X * v) = cornL X := by
  unfold cornL
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  by_cases hc : (i : ℕ) = 0 ∧ (j : ℕ) + 1 = a
  · rw [if_pos hc, if_pos hc, Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hv.2 j, mul_one]
    · intro k _ hk
      have hk' : (k : ℕ) ≠ j := fun e => hk (Fin.ext e)
      have hkj : k < j := by
        rw [Fin.lt_iff_val_lt_val]
        have := k.2
        omega
      rw [hv.1 hkj, mul_zero]
    · simp
  · rw [if_neg hc, if_neg hc]

theorem cornU_mul_up {u : Matrix (Fin a) (Fin a) K} (hu : IsUpUni u)
    (Y : Matrix (Fin a) (Fin s) K) : cornU (u * Y) = cornU Y := by
  unfold cornU
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hc : (j : ℕ) = 0 ∧ (i : ℕ) + 1 = a
  · rw [if_pos hc, if_pos hc, Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hu.2 i, one_mul]
    · intro k _ hk
      have hk' : (k : ℕ) ≠ i := fun e => hk (Fin.ext e)
      have hki : k < i := by
        rw [Fin.lt_iff_val_lt_val]
        have := k.2
        omega
      rw [hu.1 hki, zero_mul]
    · simp
  · rw [if_neg hc, if_neg hc]

end Simple

section Lists

theorem revIn_append_lt (l' : List ℕ) : ∀ (l : List ℕ) (j : ℕ), j < l.sum →
    revIn (l ++ l') j = revIn l j
  | [], j, h => by simp at h
  | b :: l, j, h => by
    simp only [List.cons_append, revIn]
    by_cases hj : j < b
    · rw [if_pos hj, if_pos hj]
    · rw [if_neg hj, if_neg hj, revIn_append_lt l' l (j - b) (by simp at h; omega)]

theorem revIn_append_ge (l' : List ℕ) : ∀ (l : List ℕ) (j : ℕ),
    revIn (l ++ l') (l.sum + j) = l.sum + revIn l' j
  | [], j => by simp
  | b :: l, j => by
    simp only [List.cons_append, revIn, List.sum_cons]
    rw [if_neg (by omega), show b + l.sum + j - b = l.sum + j by omega, revIn_append_ge l' l j]
    omega

theorem blk_append_lt (l' : List ℕ) : ∀ (l : List ℕ) (j : ℕ), j < l.sum →
    blk (l ++ l') j = blk l j
  | [], j, h => by simp at h
  | b :: l, j, h => by
    simp only [List.cons_append, blk]
    by_cases hj : j < b
    · rw [if_pos hj, if_pos hj]
    · rw [if_neg hj, if_neg hj, blk_append_lt l' l (j - b) (by simp at h; omega)]

theorem blk_append_ge (l' : List ℕ) : ∀ (l : List ℕ) (j : ℕ),
    blk (l ++ l') (l.sum + j) = l.length + blk l' j
  | [], j => by simp
  | b :: l, j => by
    simp only [List.cons_append, blk, List.sum_cons, List.length_cons]
    rw [if_neg (by omega), show b + l.sum + j - b = l.sum + j by omega, blk_append_ge l' l j]
    omega

variable {K : Type} [CommRing K]

private lemma blk_lt_lemma : ∀ (l : List ℕ) (j : ℕ), j < l.sum → blk l j < l.length := by
  intro l
  induction l with
  | nil =>
    intro j hj
    simp at hj
  | cons x l ih =>
    intro j hj
    rw [List.sum_cons] at hj
    simp only [blk, List.length_cons]
    by_cases h : j < x
    · rw [if_pos h]
      omega
    · rw [if_neg h]
      have := ih (j - x) (by omega)
      omega

private lemma revIn_lt_lemma_2 : ∀ (l : List ℕ) (j : ℕ), j < l.sum → revIn l j < l.sum := by
  intro l
  induction l with
  | nil =>
    intro j hj
    simp at hj
  | cons x l ih =>
    intro j hj
    rw [List.sum_cons] at hj ⊢
    simp only [revIn]
    by_cases h : j < x
    · rw [if_pos h]
      omega
    · rw [if_neg h]
      have := ih (j - x) (by omega)
      omega

private lemma revIn_invol_lemma_3 : ∀ (l : List ℕ) (j : ℕ), j < l.sum → revIn l (revIn l j) = j := by
  intro l
  induction l with
  | nil =>
    intro j hj
    simp at hj
  | cons x l ih =>
    intro j hj
    rw [List.sum_cons] at hj
    by_cases h : j < x
    · have e1 : revIn (x :: l) j = x - 1 - j := by
        simp only [revIn]
        rw [if_pos h]
      have h' : x - 1 - j < x := by omega
      have e2 : revIn (x :: l) (x - 1 - j) = x - 1 - (x - 1 - j) := by
        simp only [revIn]
        rw [if_pos h']
      rw [e1, e2]
      omega
    · have e1 : revIn (x :: l) j = x + revIn l (j - x) := by
        simp only [revIn]
        rw [if_neg h]
      have h' : ¬ (x + revIn l (j - x) < x) := by omega
      have e2 : revIn (x :: l) (x + revIn l (j - x)) = x + revIn l (x + revIn l (j - x) - x) := by
        simp only [revIn]
        rw [if_neg h']
      rw [e1, e2, show x + revIn l (j - x) - x = revIn l (j - x) by omega, ih (j - x) (by omega)]
      omega

private lemma blk_revIn_lemma_4 : ∀ (l : List ℕ) (j : ℕ), j < l.sum → blk l (revIn l j) = blk l j := by
  intro l
  induction l with
  | nil =>
    intro j hj
    simp at hj
  | cons x l ih =>
    intro j hj
    rw [List.sum_cons] at hj
    by_cases h : j < x
    · have e1 : revIn (x :: l) j = x - 1 - j := by
        simp only [revIn]
        rw [if_pos h]
      have h' : x - 1 - j < x := by omega
      have e2 : blk (x :: l) (x - 1 - j) = 0 := by
        simp only [blk]
        rw [if_pos h']
      have e3 : blk (x :: l) j = 0 := by
        simp only [blk]
        rw [if_pos h]
      rw [e1, e2, e3]
    · have e1 : revIn (x :: l) j = x + revIn l (j - x) := by
        simp only [revIn]
        rw [if_neg h]
      have h' : ¬ (x + revIn l (j - x) < x) := by omega
      have e2 : blk (x :: l) (x + revIn l (j - x)) = 1 + blk l (x + revIn l (j - x) - x) := by
        simp only [blk]
        rw [if_neg h']
      have e3 : blk (x :: l) j = 1 + blk l (j - x) := by
        simp only [blk]
        rw [if_neg h]
      rw [e1, e2, e3, show x + revIn l (j - x) - x = revIn l (j - x) by omega, ih (j - x) (by omega)]

private lemma pt_unit_lemma_5 (s : List ℕ) (t : ℕ → Kˣ) : IsUnit (pt s t).det := by
  refine Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun b c : Fin s.sum =>
    if (c : ℕ) = revIn s b then (((t (blk s b))⁻¹ : Kˣ) : K) else 0) ?_
  ext a c
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨revIn s a, revIn_lt_lemma_2 s a a.2⟩]
  · by_cases hca : c = a
    · subst hca
      simp [pt, revIn_invol_lemma_3 s c c.2, blk_revIn_lemma_4 s c c.2]
    · have h1 : (c : ℕ) ≠ a := fun e => hca (Fin.ext e)
      have h2 : a ≠ c := fun e => hca e.symm
      simp [pt, revIn_invol_lemma_3 s a a.2, blk_revIn_lemma_4 s a a.2, Matrix.one_apply, h1, h2]
  · intro b _ hb
    have : (b : ℕ) ≠ revIn s a := fun e => hb (Fin.ext e)
    simp [pt, this]
  · simp

theorem pt_append (l l' : List ℕ) (T T₁ T₂ : ℕ → Kˣ) (h₁ : ∀ b, b < l.length → T b = T₁ b)
    (h₂ : ∀ b, b < l'.length → T (l.length + b) = T₂ b) (hN : (l ++ l').sum = l.sum + l'.sum) :
    pt (l ++ l') T = blkM hN (pt l T₁) 0 0 (pt l' T₂) := by
  ext x y
  obtain ⟨p, rfl⟩ := (eN hN).surjective x
  obtain ⟨q, rfl⟩ := (eN hN).surjective y
  rcases p with i | i <;> rcases q with j | j
  · rw [blkM_ll]
    simp only [pt, eN_inl]
    rw [revIn_append_lt l' l i i.2, blk_append_lt l' l i i.2, h₁ _ (blk_lt_lemma l i i.2)]
  · rw [blkM_lr]
    simp only [pt, eN_inl, eN_inr]
    rw [revIn_append_lt l' l i i.2]
    have := revIn_lt_lemma_2 l i i.2
    simp [show ¬ (l.sum + (j : ℕ) = revIn l i) by omega]
  · rw [blkM_rl]
    simp only [pt, eN_inl, eN_inr]
    rw [revIn_append_ge l' l i]
    have := j.2
    simp [show ¬ ((j : ℕ) = l.sum + revIn l' i) by omega]
  · rw [blkM_rr]
    simp only [pt, eN_inr]
    rw [revIn_append_ge l' l i, blk_append_ge l' l i, h₂ _ (blk_lt_lemma l' i i.2)]
    simp only [Nat.add_left_cancel_iff]

theorem pt_append' (L l l' : List ℕ) (hL : L = l ++ l') (T T₁ T₂ : ℕ → Kˣ)
    (h₁ : ∀ b, b < l.length → T b = T₁ b) (h₂ : ∀ b, b < l'.length → T (l.length + b) = T₂ b)
    (hN : L.sum = l.sum + l'.sum) : pt L T = blkM hN (pt l T₁) 0 0 (pt l' T₂) := by
  subst hL
  exact pt_append l l' T T₁ T₂ h₁ h₂ hN

theorem two_block_point_size_sum (h : Point K) (m : ℕ) (t c : Kˣ) :
    (pt2 h m t c).1.sum = h.1.sum + (pt2 (h0 : Point K) m t c).1.sum := by
  simp [pt2, h0, addBlock, List.sum_append, add_assoc]

theorem two_block_point_block_matrix (h : Point K) (m : ℕ) (t c : Kˣ) :
    pt (pt2 h m t c).1 (pt2 h m t c).2 =
      blkM (two_block_point_size_sum h m t c) (pt h.1 h.2) 0 0
        (pt (pt2 (h0 : Point K) m t c).1 (pt2 (h0 : Point K) m t c).2) := by
  refine pt_append' _ h.1 _ ?_ _ h.2 _ ?_ ?_ (two_block_point_size_sum h m t c)
  · simp [pt2, h0, addBlock]
  · intro b hb
    simp [pt2, addBlock, Function.update_apply, show b ≠ h.1.length by omega,
      show b ≠ h.1.length + 1 by omega]
  · intro b hb
    have hb2 : b < 2 := by simpa [pt2, h0, addBlock] using hb
    interval_cases b <;> simp [pt2, h0, addBlock, Function.update_apply]

theorem add_sum (h : Point K) (s : ℕ) (z : Kˣ) :
    (addBlock h s z).1.sum = h.1.sum + (addBlock (h0 : Point K) s z).1.sum := by
  simp [addBlock, h0, List.sum_append]

theorem add_blk (h : Point K) (s : ℕ) (z : Kˣ) :
    pt (addBlock h s z).1 (addBlock h s z).2 =
      blkM (add_sum h s z) (pt h.1 h.2) 0 0
        (pt (addBlock (h0 : Point K) s z).1 (addBlock (h0 : Point K) s z).2) := by
  refine pt_append' _ h.1 _ ?_ _ h.2 _ ?_ ?_ (add_sum h s z)
  · simp [addBlock, h0]
  · intro b hb
    exact Function.update_of_ne (Nat.ne_of_lt hb) _ _
  · intro b hb
    have hb0 : b = 0 := by simpa [addBlock, h0] using hb
    subst hb0
    simp [addBlock, h0]

end Lists

section Cls
variable {K : Type} [CommRing K] (R : Subring K) {ι κ μ : Type}

theorem sec_clsM_outM (q : Matrix ι κ (KR R)) : clsM R (outM R q) = q := by
  ext i j
  exact Quotient.out_eq (q i j)

theorem sec_clsM_eq (x x' : Matrix ι κ K) : clsM R x = clsM R x' ↔ ∀ i j, (x' - x) i j ∈ R := by
  rw [eq_comm]
  constructor
  · intro h i j
    have h1 := congrFun (congrFun h i) j
    change Submodule.Quotient.mk (x' i j) = Submodule.Quotient.mk (x i j) at h1
    rw [Submodule.Quotient.eq, LinearMap.mem_range] at h1
    obtain ⟨r, hr⟩ := h1
    rw [Matrix.sub_apply, ← hr]
    exact r.2
  · intro h
    ext i j
    change Submodule.Quotient.mk (x' i j) = Submodule.Quotient.mk (x i j)
    rw [Submodule.Quotient.eq, LinearMap.mem_range]
    exact ⟨⟨_, h i j⟩, rfl⟩

theorem int_mul [Fintype κ] {X : Matrix ι κ K} {Y : Matrix κ μ K} (hX : ∀ i j, X i j ∈ R)
    (hY : ∀ i j, Y i j ∈ R) (i : ι) (j : μ) : (X * Y) i j ∈ R := by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hX i k) (hY k j)

end Cls

section Grp
variable {K : Type} [CommRing K] {h g w : Point K} (hN : w.1.sum = h.1.sum + g.1.sum)
  (hW : pt w.1 w.2 = blkM hN (pt h.1 h.2) 0 0 (pt g.1 g.2))

include hW in
theorem low_mem (A : Matrix (Fin h.1.sum) (Fin h.1.sum) K)
    (C : Matrix (Fin g.1.sum) (Fin h.1.sum) K) (D : Matrix (Fin g.1.sum) (Fin g.1.sum) K) :
    (IsLowUni (blkM hN A 0 C D) ∧ ∃ H : Matrix (Fin w.1.sum) (Fin w.1.sum) K, IsLowUni H ∧
      blkM hN A 0 C D * pt w.1 w.2 = pt w.1 w.2 * H) ↔
    (IsLowUni A ∧ ∃ H : Matrix (Fin h.1.sum) (Fin h.1.sum) K, IsLowUni H ∧
      A * pt h.1 h.2 = pt h.1 h.2 * H) ∧
    (IsLowUni D ∧ ∃ H : Matrix (Fin g.1.sum) (Fin g.1.sum) K, IsLowUni H ∧
      D * pt g.1 g.2 = pt g.1 g.2 * H) := by
  rw [hW]
  constructor
  · rintro ⟨hL, H, hH, e⟩
    obtain ⟨hA, -, hD⟩ := (blkM_isLowUni _ _ _ _ _).1 hL
    obtain ⟨H1, H2, H3, H4, rfl⟩ : ∃ H1 H2 H3 H4, H = blkM hN H1 H2 H3 H4 :=
      ⟨_, _, _, _, eq_blkM hN H⟩
    obtain ⟨hH1, -, hH4⟩ := (blkM_isLowUni _ _ _ _ _).1 hH
    rw [blkM_mul, blkM_mul] at e
    obtain ⟨e1, -, -, e4⟩ := blkM_inj hN e
    refine ⟨⟨hA, H1, hH1, ?_⟩, ⟨hD, H4, hH4, ?_⟩⟩
    · simpa using e1
    · simpa using e4
  · rintro ⟨⟨hA, H1, hH1, e1⟩, ⟨hD, H4, hH4, e4⟩⟩
    have hu := pt_unit_lemma_5 g.1 g.2
    refine ⟨(blkM_isLowUni _ _ _ _ _).2 ⟨hA, rfl, hD⟩,
      blkM hN H1 0 ((pt g.1 g.2)⁻¹ * C * pt h.1 h.2) H4,
      (blkM_isLowUni _ _ _ _ _).2 ⟨hH1, rfl, hH4⟩, ?_⟩
    rw [blkM_mul, blkM_mul]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    rw [e1, e4, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

def lowJ (v : lowW K h.1 h.2 × lowW K g.1 g.2) (X : Matrix (Fin g.1.sum) (Fin h.1.sum) K) :
    lowW K w.1 w.2 :=
  ⟨sec_gl (blkM hN (sec_m v.1) 0 (X * sec_m v.1) (sec_m v.2))
    (isLowUni_det K ((blkM_isLowUni _ _ _ _ _).2 ⟨v.1.2.1, rfl, v.2.2.1⟩)),
    (low_mem hN hW (sec_m v.1) (X * sec_m v.1) (sec_m v.2)).2 ⟨v.1.2, v.2.2⟩⟩

theorem lowJ_m (v : lowW K h.1 h.2 × lowW K g.1 g.2) (X : Matrix (Fin g.1.sum) (Fin h.1.sum) K) :
    sec_m (lowJ hN hW v X) = blkM hN (sec_m v.1) 0 (X * sec_m v.1) (sec_m v.2) := rfl

def upJ (u : upUniG K h.1.sum × upUniG K g.1.sum) (Y : Matrix (Fin h.1.sum) (Fin g.1.sum) K) :
    upUniG K w.1.sum :=
  ⟨sec_gl (blkM hN (sec_m u.1) (sec_m u.1 * Y) 0 (sec_m u.2))
    (isUpUni_det K ((blkM_isUpUni _ _ _ _ _).2 ⟨u.1.2, rfl, u.2.2⟩)),
    (blkM_isUpUni _ _ _ _ _).2 ⟨u.1.2, rfl, u.2.2⟩⟩

theorem upJ_m (u : upUniG K h.1.sum × upUniG K g.1.sum) (Y : Matrix (Fin h.1.sum) (Fin g.1.sum) K) :
    sec_m (upJ hN u Y) = blkM hN (sec_m u.1) (sec_m u.1 * Y) 0 (sec_m u.2) := rfl

theorem orbZ_J (v : lowW K h.1 h.2 × lowW K g.1 g.2) (u : upUniG K h.1.sum × upUniG K g.1.sum)
    (X : Matrix (Fin g.1.sum) (Fin h.1.sum) K) (Y : Matrix (Fin h.1.sum) (Fin g.1.sum) K) :
    orbZ w (lowJ hN hW v X, upJ hN u Y) =
      bigZ hN (orbZ h (v.1, u.1)) X Y (orbZ g (v.2, u.2)) := by
  have e1 : orbZ w (lowJ hN hW v X, upJ hN u Y) =
      sec_m (lowJ hN hW v X) * pt w.1 w.2 * sec_m (upJ hN u Y) := rfl
  rw [e1, lowJ_m, upJ_m, hW, blkM_mul, blkM_mul]
  unfold bigZ orbZ
  congr 1 <;>
    simp only [sec_m, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one,
      Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] <;> abel

theorem lowJ_mul (a v : lowW K h.1 h.2 × lowW K g.1 g.2)
    (ρ ξ : Matrix (Fin g.1.sum) (Fin h.1.sum) K) :
    lowJ hN hW a ρ * lowJ hN hW v ξ =
      lowJ hN hW (a * v) (ρ + sec_m a.2 * ξ * (sec_m a.1)⁻¹) := by
  apply sec_m_ext
  have hm : ∀ {n : ℕ} {H : Subgroup (GL (Fin n) K)} (x y : H), sec_m (x * y) = sec_m x * sec_m y :=
    fun _ _ => rfl
  have hi : ∀ M : Matrix (Fin h.1.sum) (Fin h.1.sum) K, (sec_m a.1)⁻¹ * (sec_m a.1 * M) = M := by
    intro M
    rw [← Matrix.mul_assoc, ← Matrix.coe_units_inv, Units.inv_mul, Matrix.one_mul]
  rw [hm, lowJ_m, lowJ_m, lowJ_m, blkM_mul, Prod.fst_mul, Prod.snd_mul, hm, hm]
  congr 1 <;>
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, hi]

theorem lowJ_surj (V : lowW K w.1 w.2) : ∃ v ξ, V = lowJ hN hW v ξ := by
  obtain ⟨A, B, C, D, hM⟩ : ∃ A B C D, ((V : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) =
      blkM hN A B C D := ⟨_, _, _, _, eq_blkM hN _⟩
  obtain ⟨hL, H, hH, e⟩ := V.2
  rw [hM] at hL e
  obtain ⟨hA, rfl, hD⟩ := (blkM_isLowUni _ _ _ _ _).1 hL
  obtain ⟨⟨-, hAm⟩, ⟨-, hDm⟩⟩ := (low_mem hN hW A C D).1 ⟨hL, H, hH, e⟩
  have hAd := isLowUni_det K hA
  have hDd := isLowUni_det K hD
  have m1 : IsLowUni ((sec_gl A hAd : GL (Fin h.1.sum) K) : Matrix (Fin h.1.sum) (Fin h.1.sum) K) ∧
      ∃ H' : Matrix (Fin h.1.sum) (Fin h.1.sum) K, IsLowUni H' ∧
        ((sec_gl A hAd : GL (Fin h.1.sum) K) : Matrix (Fin h.1.sum) (Fin h.1.sum) K) * pt h.1 h.2 =
          pt h.1 h.2 * H' := by
    rw [sec_gl_coe]
    exact ⟨hA, hAm⟩
  have m2 : IsLowUni ((sec_gl D hDd : GL (Fin g.1.sum) K) : Matrix (Fin g.1.sum) (Fin g.1.sum) K) ∧
      ∃ H' : Matrix (Fin g.1.sum) (Fin g.1.sum) K, IsLowUni H' ∧
        ((sec_gl D hDd : GL (Fin g.1.sum) K) : Matrix (Fin g.1.sum) (Fin g.1.sum) K) * pt g.1 g.2 =
          pt g.1 g.2 * H' := by
    rw [sec_gl_coe]
    exact ⟨hD, hDm⟩
  refine ⟨(⟨sec_gl A hAd, m1⟩, ⟨sec_gl D hDd, m2⟩), C * A⁻¹, sec_m_ext ?_⟩
  rw [lowJ_m]
  simp only [sec_m, sec_gl_coe]
  rw [hM, Matrix.mul_assoc, Matrix.nonsing_inv_mul A (by rw [hAd]; exact isUnit_one), Matrix.mul_one]

theorem lowJ_inj {v v' : lowW K h.1 h.2 × lowW K g.1 g.2}
    {ξ ξ' : Matrix (Fin g.1.sum) (Fin h.1.sum) K}
    (e : lowJ hN hW v ξ = lowJ hN hW v' ξ') : v = v' ∧ ξ = ξ' := by
  have e1 := congrArg sec_m e
  rw [lowJ_m, lowJ_m] at e1
  obtain ⟨h1, -, h3, h4⟩ := blkM_inj hN e1
  have hv1 : v.1 = v'.1 := sec_m_ext h1
  refine ⟨Prod.ext hv1 (sec_m_ext h4), ?_⟩
  rw [hv1] at h3
  have hv : ∀ M : Matrix (Fin g.1.sum) (Fin h.1.sum) K,
      M * sec_m v'.1 * (((v'.1 : GL (Fin h.1.sum) K)⁻¹ : GL (Fin h.1.sum) K) :
        Matrix (Fin h.1.sum) (Fin h.1.sum) K) = M := by
    intro M
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [← hv ξ, h3, hv ξ']

theorem lowJ_int (R : Subring K) (a : lowW K h.1 h.2 × lowW K g.1 g.2)
    (ρ : Matrix (Fin g.1.sum) (Fin h.1.sum) K) :
    lowJ hN hW a ρ ∈ intSub R (lowW K w.1 w.2) ↔
      (a.1 ∈ intSub R (lowW K h.1 h.2) ∧ a.2 ∈ intSub R (lowW K g.1 g.2)) ∧ ∀ i j, ρ i j ∈ R := by
  rw [sec_mem_int (R := R) (g := lowJ hN hW a ρ) (by
      rw [lowJ_m]
      exact isLowUni_det K ((blkM_isLowUni _ _ _ _ _).2 ⟨a.1.2.1, rfl, a.2.2.1⟩)),
    sec_mem_int (R := R) (g := a.1) (isLowUni_det K a.1.2.1),
    sec_mem_int (R := R) (g := a.2) (isLowUni_det K a.2.2.1), lowJ_m, blkM_isInt]
  constructor
  · rintro ⟨h1, -, h3, h4⟩
    refine ⟨⟨h1, h4⟩, ?_⟩
    have hinv := ((sec_mem_int (R := R) (g := a.1) (isLowUni_det K a.1.2.1)).2 h1).2
    have e : ρ = ρ * sec_m a.1 * (((a.1 : GL (Fin h.1.sum) K)⁻¹ : GL (Fin h.1.sum) K) :
        Matrix (Fin h.1.sum) (Fin h.1.sum) K) := by
      rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    intro i j
    rw [e]
    exact int_mul R h3 hinv i j
  · rintro ⟨⟨h1, h4⟩, h3⟩
    exact ⟨h1, fun i j => by simp, int_mul R h3 h1, h4⟩

theorem low_bij (R : Subring K) :
    Function.Bijective (fun p : (Quotient (QuotientGroup.rightRel (intSub R (lowW K h.1 h.2))) ×
        Quotient (QuotientGroup.rightRel (intSub R (lowW K g.1 g.2)))) ×
        Matrix (Fin g.1.sum) (Fin h.1.sum) (KR R) =>
      (Quotient.mk (QuotientGroup.rightRel (intSub R (lowW K w.1 w.2)))
        (lowJ hN hW (p.1.1.out, p.1.2.out) (outM R p.2)))) := by
  have key : ∀ (a a' : lowW K h.1 h.2 × lowW K g.1 g.2) (x x' : Matrix (Fin g.1.sum) (Fin h.1.sum) K),
      Quotient.mk (QuotientGroup.rightRel (intSub R (lowW K w.1 w.2))) (lowJ hN hW a x) =
        Quotient.mk (QuotientGroup.rightRel (intSub R (lowW K w.1 w.2))) (lowJ hN hW a' x') →
      ∃ b : lowW K h.1 h.2 × lowW K g.1 g.2, ∃ ρ : Matrix (Fin g.1.sum) (Fin h.1.sum) K,
        (b.1 ∈ intSub R (lowW K h.1 h.2) ∧ b.2 ∈ intSub R (lowW K g.1 g.2)) ∧ (∀ i j, ρ i j ∈ R) ∧
          a' = b * a ∧ x' = ρ + sec_m b.2 * x * (sec_m b.1)⁻¹ := by
    intro a a' x x' e
    obtain ⟨k, hk, e2⟩ := (sec_right_eq _ _ _).1 e
    obtain ⟨b, ρ, rfl⟩ := lowJ_surj hN hW k
    rw [lowJ_mul] at e2
    obtain ⟨h1, h2⟩ := lowJ_inj hN hW e2
    exact ⟨b, ρ, ((lowJ_int hN hW R b ρ).1 hk).1, ((lowJ_int hN hW R b ρ).1 hk).2, h1, h2⟩
  have conv : ∀ (a b : lowW K h.1 h.2 × lowW K g.1 g.2) (x ρ : Matrix (Fin g.1.sum) (Fin h.1.sum) K),
      (b.1 ∈ intSub R (lowW K h.1 h.2) ∧ b.2 ∈ intSub R (lowW K g.1 g.2)) → (∀ i j, ρ i j ∈ R) →
      Quotient.mk (QuotientGroup.rightRel (intSub R (lowW K w.1 w.2))) (lowJ hN hW a x) =
        Quotient.mk (QuotientGroup.rightRel (intSub R (lowW K w.1 w.2)))
          (lowJ hN hW (b * a) (ρ + sec_m b.2 * x * (sec_m b.1)⁻¹)) := by
    intro a b x ρ hb hρ
    exact (sec_right_eq _ _ _).2 ⟨lowJ hN hW b ρ, (lowJ_int hN hW R b ρ).2 ⟨hb, hρ⟩,
      (lowJ_mul hN hW b a ρ x).symm⟩
  refine sec_fib
    (fun a : lowW K h.1 h.2 × lowW K g.1 g.2 =>
      (Quotient.mk (QuotientGroup.rightRel (intSub R (lowW K h.1 h.2))) a.1,
        Quotient.mk (QuotientGroup.rightRel (intSub R (lowW K g.1 g.2))) a.2))
    (fun q => (q.1.out, q.2.out))
    (fun q => Prod.ext (Quotient.out_eq q.1) (Quotient.out_eq q.2))
    (clsM R) (outM R) (sec_clsM_outM R)
    (Quotient.mk (QuotientGroup.rightRel (intSub R (lowW K w.1 w.2))))
    Quotient.mk_surjective (fun a x => lowJ hN hW a x) (lowJ_surj hN hW) ?_ ?_ ?_
  · intro a x a' x' e
    obtain ⟨b, ρ, ⟨hb1, hb2⟩, -, rfl, -⟩ := key a a' x x' e
    refine Prod.ext ((sec_right_eq _ _ _).2 ⟨b.1, hb1, ?_⟩) ((sec_right_eq _ _ _).2 ⟨b.2, hb2, ?_⟩)
    · rfl
    · rfl
  · intro a x x'
    constructor
    · intro e
      obtain ⟨b, ρ, -, hρ, hab, rfl⟩ := key a a x x' e
      have hb : b = 1 := mul_right_cancel (hab.symm.trans (one_mul a).symm)
      subst hb
      rw [sec_clsM_eq]
      intro i j
      simpa [sec_m] using hρ i j
    · intro e
      rw [sec_clsM_eq] at e
      have := conv a 1 x (x' - x) ⟨one_mem _, one_mem _⟩ e
      simpa [sec_m] using this
  · intro a a' e x
    simp only [Prod.mk.injEq] at e
    obtain ⟨e1, e2⟩ := e
    obtain ⟨g1, hg1, hg1e⟩ := (sec_right_eq _ _ _).1 e1
    obtain ⟨g2, hg2, hg2e⟩ := (sec_right_eq _ _ _).1 e2
    refine ⟨sec_m (a' * a⁻¹).2 * x * (sec_m (a' * a⁻¹).1)⁻¹, ?_⟩
    have m1 : (a' * a⁻¹).1 ∈ intSub R (lowW K h.1 h.2) := by
      rw [show (a' * a⁻¹).1 = g1 by simp [hg1e]]
      exact hg1
    have m2 : (a' * a⁻¹).2 ∈ intSub R (lowW K g.1 g.2) := by
      rw [show (a' * a⁻¹).2 = g2 by simp [hg2e]]
      exact hg2
    have := conv a (a' * a⁻¹) x 0 ⟨m1, m2⟩ (fun i j => by simp)
    simpa using this

theorem upJ_mul (u b : upUniG K h.1.sum × upUniG K g.1.sum)
    (η ρ : Matrix (Fin h.1.sum) (Fin g.1.sum) K) :
    upJ hN u η * upJ hN b ρ = (upJ hN (u * b) (ρ + (sec_m b.1)⁻¹ * η * sec_m b.2) :
      upUniG K w.1.sum) := by
  apply sec_m_ext
  have hm : ∀ {n : ℕ} {H : Subgroup (GL (Fin n) K)} (x y : H), sec_m (x * y) = sec_m x * sec_m y :=
    fun _ _ => rfl
  have hi : ∀ M : Matrix (Fin h.1.sum) (Fin g.1.sum) K, sec_m b.1 * ((sec_m b.1)⁻¹ * M) = M := by
    intro M
    rw [← Matrix.mul_assoc, ← Matrix.coe_units_inv, Units.mul_inv, Matrix.one_mul]
  rw [hm, upJ_m, upJ_m, upJ_m, blkM_mul, Prod.fst_mul, Prod.snd_mul, hm, hm]
  congr 1 <;>
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, hi]

theorem upJ_surj (V : upUniG K w.1.sum) : ∃ u η, V = upJ hN u η := by
  obtain ⟨A, B, C, D, hM⟩ : ∃ A B C D, ((V : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) =
      blkM hN A B C D := ⟨_, _, _, _, eq_blkM hN _⟩
  have hU : IsUpUni ((V : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) := V.2
  rw [hM] at hU
  obtain ⟨hA, rfl, hD⟩ := (blkM_isUpUni _ _ _ _ _).1 hU
  have hAd := isUpUni_det K hA
  have hDd := isUpUni_det K hD
  have m1 : IsUpUni ((sec_gl A hAd : GL (Fin h.1.sum) K) : Matrix (Fin h.1.sum) (Fin h.1.sum) K) := by
    rw [sec_gl_coe]
    exact hA
  have m2 : IsUpUni ((sec_gl D hDd : GL (Fin g.1.sum) K) : Matrix (Fin g.1.sum) (Fin g.1.sum) K) := by
    rw [sec_gl_coe]
    exact hD
  refine ⟨(⟨sec_gl A hAd, m1⟩, ⟨sec_gl D hDd, m2⟩), A⁻¹ * B, sec_m_ext ?_⟩
  rw [upJ_m]
  simp only [sec_m, sec_gl_coe]
  rw [hM, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv A (by rw [hAd]; exact isUnit_one), Matrix.one_mul]

theorem upJ_inj {u u' : upUniG K h.1.sum × upUniG K g.1.sum}
    {η η' : Matrix (Fin h.1.sum) (Fin g.1.sum) K}
    (e : (upJ hN u η : upUniG K w.1.sum) = upJ hN u' η') : u = u' ∧ η = η' := by
  have e1 := congrArg sec_m e
  rw [upJ_m, upJ_m] at e1
  obtain ⟨h1, h2, -, h4⟩ := blkM_inj hN e1
  have hu1 : u.1 = u'.1 := sec_m_ext h1
  refine ⟨Prod.ext hu1 (sec_m_ext h4), ?_⟩
  rw [hu1] at h2
  have hu : ∀ M : Matrix (Fin h.1.sum) (Fin g.1.sum) K,
      (((u'.1 : GL (Fin h.1.sum) K)⁻¹ : GL (Fin h.1.sum) K) : Matrix (Fin h.1.sum) (Fin h.1.sum) K) *
        (sec_m u'.1 * M) = M := by
    intro M
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  rw [← hu η, h2, hu η']

theorem upJ_int (R : Subring K) (b : upUniG K h.1.sum × upUniG K g.1.sum)
    (ρ : Matrix (Fin h.1.sum) (Fin g.1.sum) K) :
    (upJ hN b ρ : upUniG K w.1.sum) ∈ intSub R (upUniG K w.1.sum) ↔
      (b.1 ∈ intSub R (upUniG K h.1.sum) ∧ b.2 ∈ intSub R (upUniG K g.1.sum)) ∧
        ∀ i j, ρ i j ∈ R := by
  rw [sec_mem_int (R := R) (g := (upJ hN b ρ : upUniG K w.1.sum)) (by
      rw [upJ_m]
      exact isUpUni_det K ((blkM_isUpUni _ _ _ _ _).2 ⟨b.1.2, rfl, b.2.2⟩)),
    sec_mem_int (R := R) (g := b.1) (isUpUni_det K b.1.2),
    sec_mem_int (R := R) (g := b.2) (isUpUni_det K b.2.2), upJ_m, blkM_isInt]
  constructor
  · rintro ⟨h1, h2, -, h4⟩
    refine ⟨⟨h1, h4⟩, ?_⟩
    have hinv := ((sec_mem_int (R := R) (g := b.1) (isUpUni_det K b.1.2)).2 h1).2
    have e : ρ = (((b.1 : GL (Fin h.1.sum) K)⁻¹ : GL (Fin h.1.sum) K) :
        Matrix (Fin h.1.sum) (Fin h.1.sum) K) * (sec_m b.1 * ρ) := by
      rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    intro i j
    rw [e]
    exact int_mul R hinv h2 i j
  · rintro ⟨⟨h1, h4⟩, h3⟩
    exact ⟨h1, int_mul R h1 h3, fun i j => by simp, h4⟩

theorem up_bij (R : Subring K) :
    Function.Bijective (fun p : ((upUniG K h.1.sum ⧸ intSub R (upUniG K h.1.sum)) ×
        (upUniG K g.1.sum ⧸ intSub R (upUniG K g.1.sum))) ×
        Matrix (Fin h.1.sum) (Fin g.1.sum) (KR R) =>
      ((upJ hN (p.1.1.out, p.1.2.out) (outM R p.2) : upUniG K w.1.sum) :
        upUniG K w.1.sum ⧸ intSub R (upUniG K w.1.sum))) := by
  have key : ∀ (a a' : upUniG K h.1.sum × upUniG K g.1.sum) (x x' : Matrix (Fin h.1.sum) (Fin g.1.sum) K),
      (QuotientGroup.mk (upJ hN a x) : upUniG K w.1.sum ⧸ intSub R (upUniG K w.1.sum)) =
        QuotientGroup.mk (upJ hN a' x') →
      ∃ b : upUniG K h.1.sum × upUniG K g.1.sum, ∃ ρ : Matrix (Fin h.1.sum) (Fin g.1.sum) K,
        (b.1 ∈ intSub R (upUniG K h.1.sum) ∧ b.2 ∈ intSub R (upUniG K g.1.sum)) ∧ (∀ i j, ρ i j ∈ R) ∧
          a' = a * b ∧ x' = ρ + (sec_m b.1)⁻¹ * x * sec_m b.2 := by
    intro a a' x x' e
    rw [QuotientGroup.eq] at e
    obtain ⟨b, ρ, hk⟩ := upJ_surj hN ((upJ hN a x)⁻¹ * upJ hN a' x')
    rw [hk] at e
    have e2 : upJ hN a' x' = upJ hN a x * upJ hN b ρ := by
      rw [← hk, mul_inv_cancel_left]
    rw [upJ_mul] at e2
    obtain ⟨h1, h2⟩ := upJ_inj hN e2
    exact ⟨b, ρ, ((upJ_int hN R b ρ).1 e).1, ((upJ_int hN R b ρ).1 e).2, h1, h2⟩
  have conv : ∀ (a b : upUniG K h.1.sum × upUniG K g.1.sum) (x ρ : Matrix (Fin h.1.sum) (Fin g.1.sum) K),
      (b.1 ∈ intSub R (upUniG K h.1.sum) ∧ b.2 ∈ intSub R (upUniG K g.1.sum)) → (∀ i j, ρ i j ∈ R) →
      (QuotientGroup.mk (upJ hN a x) : upUniG K w.1.sum ⧸ intSub R (upUniG K w.1.sum)) =
        QuotientGroup.mk (upJ hN (a * b) (ρ + (sec_m b.1)⁻¹ * x * sec_m b.2)) := by
    intro a b x ρ hb hρ
    rw [QuotientGroup.eq, ← upJ_mul, inv_mul_cancel_left]
    exact (upJ_int hN R b ρ).2 ⟨hb, hρ⟩
  refine sec_fib
    (fun a : upUniG K h.1.sum × upUniG K g.1.sum =>
      ((a.1 : upUniG K h.1.sum ⧸ intSub R (upUniG K h.1.sum)),
        (a.2 : upUniG K g.1.sum ⧸ intSub R (upUniG K g.1.sum))))
    (fun q => (q.1.out, q.2.out))
    (fun q => Prod.ext (QuotientGroup.out_eq' q.1) (QuotientGroup.out_eq' q.2))
    (clsM R) (outM R) (sec_clsM_outM R)
    (QuotientGroup.mk : upUniG K w.1.sum → upUniG K w.1.sum ⧸ intSub R (upUniG K w.1.sum))
    QuotientGroup.mk_surjective (fun a x => upJ hN a x) (upJ_surj hN) ?_ ?_ ?_
  · intro a x a' x' e
    obtain ⟨b, ρ, ⟨hb1, hb2⟩, -, rfl, -⟩ := key a a' x x' e
    refine Prod.ext (QuotientGroup.eq.2 ?_) (QuotientGroup.eq.2 ?_)
    · simpa using hb1
    · simpa using hb2
  · intro a x x'
    constructor
    · intro e
      obtain ⟨b, ρ, -, hρ, hab, rfl⟩ := key a a x x' e
      have hb : b = 1 := mul_left_cancel (hab.symm.trans (mul_one a).symm)
      subst hb
      rw [sec_clsM_eq]
      intro i j
      simpa [sec_m] using hρ i j
    · intro e
      rw [sec_clsM_eq] at e
      have := conv a 1 x (x' - x) ⟨one_mem _, one_mem _⟩ e
      simpa [sec_m] using this
  · intro a a' e x
    simp only [Prod.mk.injEq] at e
    obtain ⟨e1, e2⟩ := e
    rw [QuotientGroup.eq] at e1 e2
    refine ⟨(sec_m (a⁻¹ * a').1)⁻¹ * x * sec_m (a⁻¹ * a').2, ?_⟩
    have := conv a (a⁻¹ * a') x 0 ⟨by simpa using e1, by simpa using e2⟩ (fun i j => by simp)
    simpa using this

end Grp

section PhiInv
variable {K : Type} [CommRing K] (R : Subring K)

theorem mem_mul {ι κ μ : Type} [Fintype κ] {A : Matrix ι κ K} {B : Matrix κ μ K}
    (hA : ∀ i j, A i j ∈ R) (hB : ∀ i j, B i j ∈ R) (i : ι) (j : μ) : (A * B) i j ∈ R := by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hA i k) (hB k j)

theorem Fz_uni {n n' : ℕ} (Z' : Matrix (Fin n') (Fin n') K) (a0 b0 Z : Matrix (Fin n) (Fin n) K)
    (haL : IsLowUni a0) (haI : IsInt R a0) (hbU : IsUpUni b0) (hbI : IsInt R b0) :
    Fz R Z' (a0 * Z * b0) = Fz R Z' Z := by
  have hint := Formalism.DoubleCosetMeasures.P.intInv K R n a0 b0 Z haL hbU haI hbI
  have hiso : ∃ φ : coker R Z ≃ₗ[R] coker R (a0 * Z * b0), φ ∈ isoZZ R Z (a0 * Z * b0) := by
    obtain ⟨A, rfl⟩ : ∃ A : Matrix (Fin n) (Fin n) R, A.map R.subtype = a0 :=
      ⟨Formalism.DoubleCosetMeasures.P.liftR R a0 haI, Formalism.DoubleCosetMeasures.P.liftR_map R a0 haI⟩
    obtain ⟨B, rfl⟩ : ∃ B : Matrix (Fin n) (Fin n) R, B.map R.subtype = b0 :=
      ⟨Formalism.DoubleCosetMeasures.P.liftR R b0 hbI, Formalism.DoubleCosetMeasures.P.liftR_map R b0 hbI⟩
    have hA := isLowUni_det K haL
    have hB := isUpUni_det K hbU
    refine ⟨Formalism.DoubleCosetMeasures.P.cokEquiv R A B Z hA hB, Formalism.DoubleCosetMeasures.P.cokEquiv_eZ R A B Z hA hB haL,
      fun v v' hv => ?_⟩
    rw [Formalism.DoubleCosetMeasures.P.cokEquiv_mk] at hv
    rw [← Formalism.FourierDecayAlt.P.A5x4.lamLin_mk_eq R _ hv, Formalism.DoubleCosetMeasures.P.lamLin_mul R A B Z hA hbU]
  obtain ⟨φ, hφ⟩ := hiso
  unfold Fz
  rw [← Formalism.FourierDecayAlt.P.A5x4.card_isoZZ_congr R hφ (Formalism.FourierDecayAlt.P.A5x4.isoZZ_refl R Z')]
  by_cases hc : IsInt R Z
  · rw [if_pos hc, if_pos (hint.2 hc)]
  · rw [if_neg hc, if_neg (fun h => hc (hint.1 h))]

theorem clsM_outM {ι κ : Type} (x : Matrix ι κ (KR R)) : clsM R (outM R x) = x := by
  ext i j
  exact Quotient.out_eq (x i j)

theorem clsM_eq {ι κ : Type} (x x' : Matrix ι κ K) :
    clsM R x = clsM R x' ↔ ∀ i j, (x - x') i j ∈ R := by
  rw [eq_comm, sec_clsM_eq]

theorem outM_clsM {ι κ : Type} (x : Matrix ι κ K) (i : ι) (j : κ) :
    (outM R (clsM R x) - x) i j ∈ R := by
  exact (clsM_eq R (outM R (clsM R x)) x).1 (clsM_outM R (clsM R x)) i j

theorem cls_leftInv {ι κ : Type} (L L' : Matrix ι κ K → Matrix ι κ K)
    (hadd : ∀ U V, L' (U + V) = L' U + L' V)
    (hint : ∀ V, (∀ i j, V i j ∈ R) → ∀ i j, L' V i j ∈ R) (hinv : ∀ U, L' (L U) = U)
    (x : Matrix ι κ (KR R)) : clsM R (L' (outM R (clsM R (L (outM R x))))) = x := by
  rw [show outM R (clsM R (L (outM R x))) =
      L (outM R x) + (outM R (clsM R (L (outM R x))) - L (outM R x)) by abel, hadd, hinv]
  conv_rhs => rw [← clsM_outM R x]
  rw [clsM_eq]
  intro i j
  have := hint _ (outM_clsM R (L (outM R x))) i j
  simpa [Matrix.add_apply, Matrix.sub_apply] using this

theorem cls_bij {ι κ : Type} (L L' : Matrix ι κ K → Matrix ι κ K)
    (hadd : ∀ U V, L (U + V) = L U + L V) (hadd' : ∀ U V, L' (U + V) = L' U + L' V)
    (hint : ∀ V, (∀ i j, V i j ∈ R) → ∀ i j, L V i j ∈ R)
    (hint' : ∀ V, (∀ i j, V i j ∈ R) → ∀ i j, L' V i j ∈ R)
    (hinv : ∀ U, L' (L U) = U) (hinv' : ∀ U, L (L' U) = U) :
    Function.Bijective (fun x : Matrix ι κ (KR R) => clsM R (L (outM R x))) := by
  refine ⟨fun x₁ x₂ e => ?_, fun y => ⟨clsM R (L' (outM R y)), cls_leftInv R L' L hadd hint hinv' y⟩⟩
  have e' : clsM R (L (outM R x₁)) = clsM R (L (outM R x₂)) := e
  exact (cls_leftInv R L L' hadd' hint' hinv x₁).symm.trans
    ((congrArg (fun y => clsM R (L' (outM R y))) e').trans (cls_leftInv R L L' hadd' hint' hinv x₂))

variable {a s : ℕ}

theorem cornL_add (X X' : Matrix (Fin s) (Fin a) K) : cornL (X + X') = cornL X + cornL X' := by
  unfold cornL
  simp only [Matrix.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  by_cases hc : (i.val = 0 ∧ j.val + 1 = a) <;> simp [hc]

theorem cornU_add (Y Y' : Matrix (Fin a) (Fin s) K) : cornU (Y + Y') = cornU Y + cornU Y' := by
  unfold cornU
  simp only [Matrix.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hc : (j.val = 0 ∧ i.val + 1 = a) <;> simp [hc]

theorem cornL_mem {X : Matrix (Fin s) (Fin a) K} (hX : ∀ i j, X i j ∈ R) : cornL X ∈ R := by
  unfold cornL
  exact sum_mem fun j _ => sum_mem fun i _ => by
    split_ifs
    exacts [hX i j, zero_mem _]

theorem cornU_mem {Y : Matrix (Fin a) (Fin s) K} (hY : ∀ i j, Y i j ∈ R) : cornU Y ∈ R := by
  unfold cornU
  exact sum_mem fun i _ => sum_mem fun j _ => by
    split_ifs
    exacts [hY i j, zero_mem _]

theorem cornL_low_mul {v : Matrix (Fin s) (Fin s) K} (hv : IsLowUni v) (X : Matrix (Fin s) (Fin a) K) :
    cornL (v * X) = cornL X := by
  unfold cornL
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  by_cases hc : (i : ℕ) = 0 ∧ (j : ℕ) + 1 = a
  · rw [if_pos hc, if_pos hc, Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hv.2 i, one_mul]
    · intro k _ hk
      have hk' : (k : ℕ) ≠ i := fun e => hk (Fin.ext e)
      have hik : i < k := by
        rw [Fin.lt_iff_val_lt_val]
        omega
      rw [hv.1 hik, zero_mul]
    · simp
  · rw [if_neg hc, if_neg hc]

theorem cornU_mul_up' {u : Matrix (Fin s) (Fin s) K} (hu : IsUpUni u) (Y : Matrix (Fin a) (Fin s) K) :
    cornU (Y * u) = cornU Y := by
  unfold cornU
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hc : (j : ℕ) = 0 ∧ (i : ℕ) + 1 = a
  · rw [if_pos hc, if_pos hc, Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hu.2 j, mul_one]
    · intro k _ hk
      have hk' : (k : ℕ) ≠ j := fun e => hk (Fin.ext e)
      have hjk : j < k := by
        rw [Fin.lt_iff_val_lt_val]
        omega
      rw [hu.1 hjk, mul_zero]
    · simp
  · rw [if_neg hc, if_neg hc]

variable {N : ℕ}

theorem bigZ_translate (hN : N = a + s) (Z1 : Matrix (Fin a) (Fin a) K)
    (X X0 : Matrix (Fin s) (Fin a) K) (Y Y0 : Matrix (Fin a) (Fin s) K)
    (G : Matrix (Fin s) (Fin s) K) :
    bigZ hN Z1 (X + X0) (Y + Y0) G =
      blkM hN 1 0 X0 1 * bigZ hN Z1 X Y G * blkM hN 1 Y0 0 1 := by
  unfold bigZ
  rw [blkM_mul, blkM_mul]
  congr 1 <;>
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one,
      Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] <;> abel

theorem bigZ_conj (hN : N = a + s) (Z1 : Matrix (Fin a) (Fin a) K)
    (X : Matrix (Fin s) (Fin a) K) (Y : Matrix (Fin a) (Fin s) K)
    (G v u : Matrix (Fin s) (Fin s) K) :
    bigZ hN Z1 (v * X) (Y * u) (v * G * u) =
      blkM hN 1 0 0 v * bigZ hN Z1 X Y G * blkM hN 1 0 0 u := by
  unfold bigZ
  rw [blkM_mul, blkM_mul]
  congr 1 <;>
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one,
      Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] <;> abel

def Tsum (ψ : AddChar K ℂ) {n' : ℕ} (Z' : Matrix (Fin n') (Fin n') K)
    (Z1 : Matrix (Fin a) (Fin a) K) (X : Matrix (Fin s) (Fin a) K) (Y : Matrix (Fin a) (Fin s) K)
    (G : Matrix (Fin s) (Fin s) K) : ℂ :=
  Fz R Z' (bigZ rfl Z1 X Y G) * ψ (cornL X + cornU Y)

theorem Tsum_translate (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) {n' : ℕ}
    (Z' : Matrix (Fin n') (Fin n') K) (Z1 : Matrix (Fin a) (Fin a) K)
    (X X1 : Matrix (Fin s) (Fin a) K) (Y Y1 : Matrix (Fin a) (Fin s) K)
    (G : Matrix (Fin s) (Fin s) K) (hX : ∀ i j, (X1 - X) i j ∈ R) (hY : ∀ i j, (Y1 - Y) i j ∈ R) :
    Tsum R ψ Z' Z1 X1 Y1 G = Tsum R ψ Z' Z1 X Y G := by
  unfold Tsum
  have h1 : ∀ {n : ℕ}, IsInt R (1 : Matrix (Fin n) (Fin n) K) := by
    intro n i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  rw [show X1 = X + (X1 - X) by abel, show Y1 = Y + (Y1 - Y) by abel, bigZ_translate,
    Fz_uni R Z' _ _ _ ((blkM_isLowUni rfl 1 0 (X1 - X) 1).2 ⟨isLowUni_one K, rfl, isLowUni_one K⟩)
      ((blkM_isInt rfl 1 0 (X1 - X) 1 R).2 ⟨h1, fun i j => by simp, hX, h1⟩)
      ((blkM_isUpUni rfl 1 (Y1 - Y) 0 1).2 ⟨isUpUni_one K, rfl, isUpUni_one K⟩)
      ((blkM_isInt rfl 1 (Y1 - Y) 0 1 R).2 ⟨h1, hY, fun i j => by simp, h1⟩),
    cornL_add, cornU_add,
    show cornL X + cornL (X1 - X) + (cornU Y + cornU (Y1 - Y)) =
      (cornL X + cornU Y) + (cornL (X1 - X) + cornU (Y1 - Y)) by ring,
    AddChar.map_add_eq_mul, hψ _ (add_mem (cornL_mem R hX) (cornU_mem R hY)), mul_one]

theorem Tsum_conj (ψ : AddChar K ℂ) {n' : ℕ}
    (Z' : Matrix (Fin n') (Fin n') K) (Z1 : Matrix (Fin a) (Fin a) K)
    (X : Matrix (Fin s) (Fin a) K) (Y : Matrix (Fin a) (Fin s) K)
    (G v u : Matrix (Fin s) (Fin s) K) (hv : IsLowUni v) (hvi : IsInt R v) (hu : IsUpUni u)
    (hui : IsInt R u) :
    Tsum R ψ Z' Z1 (v * X) (Y * u) (v * G * u) = Tsum R ψ Z' Z1 X Y G := by
  unfold Tsum
  have h1 : ∀ {n : ℕ}, IsInt R (1 : Matrix (Fin n) (Fin n) K) := by
    intro n i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  rw [bigZ_conj,
    Fz_uni R Z' _ _ _ ((blkM_isLowUni rfl 1 0 0 v).2 ⟨isLowUni_one K, rfl, hv⟩)
      ((blkM_isInt rfl 1 0 0 v R).2 ⟨h1, fun i j => by simp, fun i j => by simp, hvi⟩)
      ((blkM_isUpUni rfl 1 0 0 u).2 ⟨isUpUni_one K, rfl, hu⟩)
      ((blkM_isInt rfl 1 0 0 u R).2 ⟨h1, fun i j => by simp, fun i j => by simp, hui⟩),
    cornL_low_mul hv, cornU_mul_up' hu]

theorem PhiH_eq_Tsum (ψ : AddChar K ℂ) (h : Point K) {n' : ℕ} (Z' : Matrix (Fin n') (Fin n') K)
    (n : ℕ) (G : Matrix (Fin n) (Fin n) K) :
    PhiH R ψ h Z' n G =
      ∑ᶠ τ : Cos R h × Matrix (Fin n) (Fin h.1.sum) (KR R) × Matrix (Fin h.1.sum) (Fin n) (KR R),
        Tsum R ψ Z' (orbZ h (rep R τ.1)) (outM R τ.2.1) (outM R τ.2.2) G * phase ψ (rep R τ.1) := by
  unfold PhiH Tsum
  exact finsum_congr fun τ => by ring

theorem PhiH_inv (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) (h : Point K) {n' : ℕ}
    (Z' : Matrix (Fin n') (Fin n') K) (s : ℕ) (Z a b : Matrix (Fin s) (Fin s) K)
    (ha : IsLowUni a) (hai : IsInt R a) (hb : IsUpUni b) (hbi : IsInt R b) :
    PhiH R ψ h Z' s (a * Z * b) = PhiH R ψ h Z' s Z := by
  have hda : a.det = 1 := isLowUni_det K ha
  have hdb : b.det = 1 := isUpUni_det K hb
  have hua : IsUnit a.det := by rw [hda]; exact isUnit_one
  have hub : IsUnit b.det := by rw [hdb]; exact isUnit_one
  have hadj : ∀ {c : Matrix (Fin s) (Fin s) K}, IsInt R c → IsInt R c.adjugate := by
    intro c hc
    have e : c = R.subtype.mapMatrix (Matrix.of fun i j => (⟨c i j, hc i j⟩ : R)) := by
      ext i j
      rfl
    rw [e, ← RingHom.map_adjugate]
    intro i j
    exact ((Matrix.adjugate (Matrix.of fun i j => (⟨c i j, hc i j⟩ : R))) i j).2
  have hinvI : ∀ {c : Matrix (Fin s) (Fin s) K}, IsInt R c → c.det = 1 → IsInt R c⁻¹ := by
    intro c hc hd
    rw [Matrix.inv_def, hd, Ring.inverse_one, one_smul]
    exact hadj hc
  have hF := cls_bij R (ι := Fin s) (κ := Fin h.1.sum) (fun U => a * U) (fun U => a⁻¹ * U)
    (fun U V => Matrix.mul_add _ _ _) (fun U V => Matrix.mul_add _ _ _)
    (fun V hV => mem_mul R hai hV) (fun V hV => mem_mul R (hinvI hai hda) hV)
    (fun U => by
      show a⁻¹ * (a * U) = U
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul a hua, Matrix.one_mul])
    (fun U => by
      show a * (a⁻¹ * U) = U
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv a hua, Matrix.one_mul])
  have hG := cls_bij R (ι := Fin h.1.sum) (κ := Fin s) (fun U => U * b) (fun U => U * b⁻¹)
    (fun U V => Matrix.add_mul _ _ _) (fun U V => Matrix.add_mul _ _ _)
    (fun V hV => mem_mul R hV hbi) (fun V hV => mem_mul R hV (hinvI hbi hdb))
    (fun U => by
      show U * b * b⁻¹ = U
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv b hub, Matrix.mul_one])
    (fun U => by
      show U * b⁻¹ * b = U
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul b hub, Matrix.mul_one])
  rw [PhiH_eq_Tsum, PhiH_eq_Tsum,
    ← finsum_comp_equiv ((Equiv.refl (Cos R h)).prodCongr
      ((Equiv.ofBijective _ hF).prodCongr (Equiv.ofBijective _ hG)))]
  refine finsum_congr fun τ => ?_
  simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply,
    Equiv.ofBijective_apply]
  rw [Tsum_translate R ψ hψ Z' _ (a * outM R τ.2.1) _ (outM R τ.2.2 * b) _ _ (outM_clsM R _)
      (outM_clsM R _),
    Tsum_conj R ψ Z' _ _ _ _ a b ha hai hb hbi]

theorem PhiH_supp (ψ : AddChar K ℂ) (h : Point K) {n' : ℕ}
    (Z' : Matrix (Fin n') (Fin n') K) (s : ℕ) (Z : Matrix (Fin s) (Fin s) K)
    (hne : PhiH R ψ h Z' s Z ≠ 0) (i j : Fin s) :
    ∃ r ∈ R, Z i j = Ring.inverse (pt h.1 h.2).det * r := by
  by_contra hcon
  push_neg at hcon
  apply hne
  unfold PhiH
  apply finsum_eq_zero_of_forall_eq_zero
  intro τ
  suffices hF : Fz R Z' (bigZ rfl (orbZ h (rep R τ.1)) (outM R τ.2.1) (outM R τ.2.2) Z) = 0 by
    rw [hF, zero_mul]
  unfold Fz
  rw [if_neg]
  intro hI
  obtain ⟨hT, hTY, hXT, hD⟩ := (blkM_isInt rfl _ _ _ _ R).1 hI
  set T := orbZ h (rep R τ.1) with hTdef
  set X := outM R τ.2.1
  set Y := outM R τ.2.2
  have hdT : T.det = (pt h.1 h.2).det := by
    rw [hTdef]
    unfold orbZ
    rw [Matrix.det_mul, Matrix.det_mul, isLowUni_det K (rep R τ.1).1.2.1, isUpUni_det K (rep R τ.1).2.2]
    ring
  have hu : IsUnit T.det := by
    rw [hdT]
    exact pt_unit_lemma_5 h.1 h.2
  have hTR : T = R.subtype.mapMatrix (Matrix.of fun a b => (⟨T a b, hT a b⟩ : R)) := by
    ext a b
    rfl
  have hadj : IsInt R T.adjugate := by
    rw [hTR, ← RingHom.map_adjugate]
    intro a b
    exact ((Matrix.adjugate (Matrix.of fun a b => (⟨T a b, hT a b⟩ : R))) a b).2
  have hdet : T.det ∈ R := by
    rw [hTR, ← RingHom.map_det]
    exact (Matrix.det (Matrix.of fun a b => (⟨T a b, hT a b⟩ : R))).2
  have hXTY : X * T * Y = Ring.inverse T.det • (X * T * T.adjugate * (T * Y)) := by
    have e1 : X * T * Y = X * T * T⁻¹ * (T * Y) := by
      rw [Matrix.mul_assoc (X * T), ← Matrix.mul_assoc T⁻¹, Matrix.nonsing_inv_mul T hu, Matrix.one_mul]
    rw [e1, Matrix.inv_def, Matrix.mul_smul, Matrix.smul_mul]
  have hm : ((X * T) * T.adjugate * (T * Y)) i j ∈ R :=
    mem_mul R (mem_mul R hXT hadj) hTY i j
  apply hcon (T.det * (X * T * Y + Z) i j - ((X * T) * T.adjugate * (T * Y)) i j)
    (R.sub_mem (R.mul_mem hdet (hD i j)) hm)
  rw [mul_sub, ← mul_assoc, ← hdT, Ring.inverse_mul_cancel _ hu, one_mul, Matrix.add_apply, hXTY,
    Matrix.smul_apply, smul_eq_mul]
  ring

end PhiInv

section Pert
variable {K : Type} [CommRing K] (R : Subring K)

theorem pert_unit (ϖ : R) (hu : ∀ r : R, IsUnit (1 + ϖ * r)) {N : ℕ}
    (M : Matrix (Fin N) (Fin N) R) : IsUnit (1 + ϖ • M).det := by
  have h0 : (Ideal.Quotient.mk (Ideal.span {ϖ})) ϖ = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self ϖ)
  have hq : (Ideal.Quotient.mk (Ideal.span {ϖ})) ((1 + ϖ • M).det) =
      (Ideal.Quotient.mk (Ideal.span {ϖ})) 1 := by
    rw [RingHom.map_det, map_one]
    have hz : (Ideal.Quotient.mk (Ideal.span {ϖ})).mapMatrix (ϖ • M) = 0 := by
      ext i j
      simp [h0]
    rw [map_add, map_one, hz, add_zero, Matrix.det_one]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hq)
  have e : (1 + ϖ • M).det = 1 + ϖ * a := by linear_combination -ha
  rw [e]
  exact hu a

theorem pert_latZ {N : ℕ} (Z : Matrix (Fin N) (Fin N) K) (g g' : Matrix (Fin N) (Fin N) R)
    (h1 : g * g' = 1) : latZ R (Z * g.map R.subtype) = latZ R Z := by
  unfold latZ
  have hc : ∀ w : Fin N → R, coeLin R w = fun i => ((w i : R) : K) := fun w => rfl
  have hmv : ∀ (A : Matrix (Fin N) (Fin N) R) (w : Fin N → R),
      (A.map R.subtype) *ᵥ (coeLin R w) = coeLin R (A *ᵥ w) := by
    intro A w
    rw [hc, hc]
    funext i
    exact (RingHom.map_mulVec R.subtype A w i).symm
  congr 1
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_range] at hx ⊢
    obtain ⟨w, rfl⟩ := hx
    refine ⟨g *ᵥ w, ?_⟩
    show Z *ᵥ coeLin R (g *ᵥ w) = (Z * g.map R.subtype) *ᵥ coeLin R w
    rw [← Matrix.mulVec_mulVec, hmv]
  · intro x hx
    rw [LinearMap.mem_range] at hx ⊢
    obtain ⟨w, rfl⟩ := hx
    refine ⟨g' *ᵥ w, ?_⟩
    show (Z * g.map R.subtype) *ᵥ coeLin R (g' *ᵥ w) = Z *ᵥ coeLin R w
    rw [← Matrix.mulVec_mulVec, hmv, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

theorem pert_lamLin {N : ℕ} (Z Z₁ W : Matrix (Fin N) (Fin N) K) (hW : IsInt R W)
    (h : Z₁⁻¹ = Z⁻¹ - W) (v : Fin N → R) : lamLin R Z₁ v = lamLin R Z v := by
  unfold lamLin
  have hc : ∀ w : Fin N → R, coeLin R w = fun i => ((w i : R) : K) := fun w => rfl
  have hWv : W *ᵥ coeLin R v =
      coeLin R ((Matrix.of fun i j => (⟨W i j, hW i j⟩ : R)) *ᵥ v) := by
    rw [hc, hc]
    funext i
    exact (RingHom.map_mulVec R.subtype (Matrix.of fun i j => (⟨W i j, hW i j⟩ : R)) v i).symm
  have hq : ∀ u : Fin N → R,
      (LinearMap.range (Algebra.linearMap R K)).mkQ (lastCoord R (coeLin R u)) = 0 := by
    intro u
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    unfold lastCoord
    rw [LinearMap.sum_apply]
    refine sum_mem fun j _ => ?_
    split_ifs
    · exact LinearMap.mem_range.2 ⟨u j, rfl⟩
    · simp
  show (LinearMap.range (Algebra.linearMap R K)).mkQ (lastCoord R (Z₁⁻¹ *ᵥ coeLin R v)) =
    (LinearMap.range (Algebra.linearMap R K)).mkQ (lastCoord R (Z⁻¹ *ᵥ coeLin R v))
  rw [h, Matrix.sub_mulVec, map_sub, map_sub, hWv, hq, sub_zero]

theorem pert_card {N n' : ℕ} (Z' : Matrix (Fin n') (Fin n') K) (Z Z₁ : Matrix (Fin N) (Fin N) K)
    (h1 : latZ R Z = latZ R Z₁) (h2 : ∀ v, lamLin R Z₁ v = lamLin R Z v) :
    Nat.card (isoZZ R Z₁ Z') = Nat.card (isoZZ R Z Z') := by
  let ψ : coker R Z ≃ₗ[R] coker R Z₁ := Submodule.quotEquivOfEq _ _ h1
  have hψe : ψ (eZ R Z) = eZ R Z₁ := rfl
  have hψm : ∀ v : Fin N → R, ψ (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := fun v => rfl
  let e : (coker R Z₁ ≃ₗ[R] coker R Z') ≃ (coker R Z ≃ₗ[R] coker R Z') :=
    ⟨fun φ => ψ.trans φ, fun φ => ψ.symm.trans φ, fun φ => by ext x; simp, fun φ => by ext x; simp⟩
  refine Nat.card_congr (e.subtypeEquiv fun φ => ?_)
  simp only [isoZZ, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1', h2'⟩
    refine ⟨?_, fun v v' hv => ?_⟩
    · show φ (ψ (eZ R Z)) = eZ R Z'
      rw [hψe, h1']
    · have hv' : φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' := by
        rw [← hψm v]
        exact hv
      rw [h2' v v' hv', h2]
  · rintro ⟨h1', h2'⟩
    refine ⟨?_, fun v v' hv => ?_⟩
    · rw [← hψe]
      exact h1'
    · have hv' : (e φ) (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' := by
        show φ (ψ (Submodule.Quotient.mk v)) = _
        rw [hψm v]
        exact hv
      rw [h2' v v' hv', h2]

theorem Fz_perturb (ϖ : K) (hϖ : ϖ ∈ R) (hu : ∀ r ∈ R, ∃ y ∈ R, (1 + ϖ * r) * y = 1) {N n' : ℕ}
    (Z' : Matrix (Fin n') (Fin n') K) (Z P : Matrix (Fin N) (Fin N) K) (hd : IsUnit Z.det)
    (hPi : IsInt R P) (hP : ∀ i j, ∃ r ∈ R, P i j = Z.det ^ 2 * (ϖ * r)) :
    Fz R Z' (Z + P) = Fz R Z' Z := by
  unfold Fz
  by_cases hZ : IsInt R Z
  swap
  · rw [if_neg hZ, if_neg]
    intro h
    apply hZ
    intro i j
    have := R.sub_mem (h i j) (hPi i j)
    simpa using this
  have hZP : IsInt R (Z + P) := fun i j => R.add_mem (hZ i j) (hPi i j)
  rw [if_pos hZ, if_pos hZP]
  congr 1

  choose p hpR hp using hP
  set d : K := Z.det with hdef
  have hdR : d ∈ R := A5x6.det_mem R Z hZ
  obtain ⟨di, hdi⟩ : ∃ di : K, d * di = 1 := ⟨_, Ring.mul_inverse_cancel d hd⟩
  have hinv : Ring.inverse d = di := by
    have := Ring.mul_inverse_cancel d hd
    calc Ring.inverse d = Ring.inverse d * (d * di) := by rw [hdi, mul_one]
      _ = (d * Ring.inverse d) * di := by ring
      _ = di := by rw [this, one_mul]
  let P₀ : Matrix (Fin N) (Fin N) K := Matrix.of p
  have hP₀ : IsInt R P₀ := fun i j => hpR i j
  have hPeq : P = (d ^ 2 * ϖ) • P₀ := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, P₀, Matrix.of_apply]
    rw [hp i j]; ring
  have hadj : IsInt R Z.adjugate := Formalism.DoubleCosetMeasures.P.isInt_adjugate R hZ
  let M' : Matrix (Fin N) (Fin N) K := Z.adjugate * (d • P₀)
  have hM' : IsInt R M' :=
    Formalism.DoubleCosetMeasures.P.isInt_mul R hadj (fun i j => by
      simp only [Matrix.smul_apply, smul_eq_mul]; exact R.mul_mem hdR (hP₀ i j))
  let ϖR : R := ⟨ϖ, hϖ⟩
  let MR : Matrix (Fin N) (Fin N) R := Formalism.DoubleCosetMeasures.P.liftR R M' hM'
  let g : Matrix (Fin N) (Fin N) R := 1 + ϖR • MR
  have huR : ∀ r : R, IsUnit (1 + ϖR * r) := by
    intro r
    obtain ⟨y, hy, e⟩ := hu r r.2
    exact IsUnit.of_mul_eq_one (⟨y, hy⟩ : R) (Subtype.ext e)
  have hgdet : IsUnit g.det := pert_unit R ϖR huR MR
  have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hgdet
  have hgmap : g.map R.subtype = 1 + ϖ • M' := by
    ext i j
    simp only [g, MR, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Formalism.DoubleCosetMeasures.P.liftR, ϖR]
    by_cases hij : i = j <;> simp [hij]
  have hZadj : Z * Z.adjugate = d • (1 : Matrix (Fin N) (Fin N) K) := Matrix.mul_adjugate Z
  have hZg : Z * g.map R.subtype = Z + P := by
    rw [hgmap, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, hZadj, hPeq]
    congr 1
    rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, smul_smul]
    congr 1; ring
  let δ : Matrix (Fin N) (Fin N) K := (g⁻¹).map R.subtype
  have hδ : IsInt R δ := fun i j => (g⁻¹ i j).2
  have hgδ : (1 + ϖ • M') * δ = 1 := by
    rw [← hgmap, ← Matrix.map_mul, hgg, Matrix.map_one _ (map_zero _) (map_one _)]
  let W : Matrix (Fin N) (Fin N) K := ϖ • (Z.adjugate * P₀ * δ * Z.adjugate)
  have hW : IsInt R W := fun i j => by
    simp only [W, Matrix.smul_apply, smul_eq_mul]
    exact R.mul_mem hϖ (Formalism.DoubleCosetMeasures.P.isInt_mul R (Formalism.DoubleCosetMeasures.P.isInt_mul R
      (Formalism.DoubleCosetMeasures.P.isInt_mul R hadj hP₀) hδ) hadj i j)
  have hZi : Z⁻¹ = di • Z.adjugate := by rw [Matrix.inv_def, ← hdef, hinv]
  have hinvZP : (Z + P)⁻¹ = Z⁻¹ - W := by
    have e1 : (Z + P)⁻¹ = δ * Z⁻¹ := by
      apply Matrix.inv_eq_right_inv
      rw [← hZg, hgmap, Matrix.mul_assoc, ← Matrix.mul_assoc _ δ, hgδ, Matrix.one_mul,
        Matrix.mul_nonsing_inv Z hd]
    have e2 : δ = 1 - (ϖ • M') * δ := by
      rw [eq_sub_iff_add_eq, ← hgδ, Matrix.add_mul, Matrix.one_mul]
    rw [e1]
    conv_lhs => rw [e2]
    rw [Matrix.sub_mul, Matrix.one_mul]
    congr 1
    rw [hZi]
    simp only [M', W, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    congr 1
    linear_combination ϖ * hdi
  refine pert_card R Z' Z (Z + P) ?_ (pert_lamLin R Z (Z + P) W hW hinvZP)
  rw [← hZg]
  exact (pert_latZ R Z g g⁻¹ hgg).symm

end Pert

theorem top_main {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ) (hD : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) :
    ∃ ϖ : Kˣ, (ϖ : K) ∈ R ∧ (∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R) ∧
      (∀ r ∈ R, ∃ y ∈ R, (1 + (ϖ : K) * r) * y = 1) ∧
      ∀ Q : Set K, IsCompact Q → (∀ d ∈ Q, IsUnit d) →
        ∃ k : ℕ, ∀ d ∈ Q, (ϖ : K) ^ k * Ring.inverse d ∈ R := by
  obtain ⟨ϖ, hϖ, hex⟩ := hD.unif
  have hpq : (ϖ : K) * ((ϖ⁻¹ : Kˣ) : K) = 1 := by simp
  refine ⟨ϖ, hϖ, hex, fun r hr => ?_, fun Q hQ hu => ?_⟩
  · obtain ⟨w, h1, _, h3⟩ := A6x4.one_add hD hn hpq hϖ hex hr
    exact ⟨w, h3, h1⟩
  · exact A6x4.inv_bounded hD hn hpq hϖ hex hQ hu

section Sum
variable {K : Type} [CommRing K] (R : Subring K) {h g w : Point K}
  (hN : w.1.sum = h.1.sum + g.1.sum)
  (hW : pt w.1 w.2 = blkM hN (pt h.1 h.2) 0 0 (pt g.1 g.2))

theorem phase_J (ψ : AddChar K ℂ) (v : lowW K h.1 h.2 × lowW K g.1 g.2)
    (u : upUniG K h.1.sum × upUniG K g.1.sum)
    (X : Matrix (Fin g.1.sum) (Fin h.1.sum) K) (Y : Matrix (Fin h.1.sum) (Fin g.1.sum) K) :
    phase ψ ((lowJ hN hW v X, upJ hN u Y) : lowW K w.1 w.2 × upUniG K w.1.sum) =
      phase ψ ((v.1, u.1) : lowW K h.1 h.2 × upUniG K h.1.sum) * ψ (cornL X + cornU Y) *
        phase ψ ((v.2, u.2) : lowW K g.1 g.2 × upUniG K g.1.sum) := by
  simp only [phase]
  rw [show ((lowJ hN hW v X : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) = _ from
      lowJ_m hN hW v X,
    show ((upJ hN u Y : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) = _ from upJ_m hN u Y,
    sLow_blkM, sUp_blkM, cornL_mul_low v.1.2.1, cornU_mul_up u.1.2,
    ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  ring

abbrev Par (h g : Point K) : Type :=
  (Cos R h × Cos R g) ×
    (Matrix (Fin g.1.sum) (Fin h.1.sum) (KR R) × Matrix (Fin h.1.sum) (Fin g.1.sum) (KR R))

def sigma (t : Par R h g) : lowW K w.1 w.2 × upUniG K w.1.sum :=
  (lowJ hN hW ((rep R t.1.1).1, (rep R t.1.2).1) (outM R t.2.1),
    upJ hN ((rep R t.1.1).2, (rep R t.1.2).2) (outM R t.2.2))

theorem sigma_bij : Function.Bijective (fun t => toCos R (sigma R hN hW t)) := by
  have hL := low_bij hN hW R
  have hU := up_bij hN R
  constructor
  · rintro ⟨⟨⟨l1, u1⟩, ⟨l2, u2⟩⟩, X, Y⟩ ⟨⟨⟨l1', u1'⟩, ⟨l2', u2'⟩⟩, X', Y'⟩ e
    have i1 : ((l1, l2), X) = ((l1', l2'), X') := hL.1 (congrArg Prod.fst e)
    have i2 : ((u1, u2), Y) = ((u1', u2'), Y') := hU.1 (congrArg Prod.snd e)
    simp only [Prod.mk.injEq] at i1 i2
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := i1
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := i2
    rfl
  · intro q
    obtain ⟨⟨⟨a1, a2⟩, X⟩, hX⟩ := hL.2 q.1
    obtain ⟨⟨⟨b1, b2⟩, Y⟩, hY⟩ := hU.2 q.2
    exact ⟨(((a1, b1), (a2, b2)), (X, Y)), Prod.ext hX hY⟩

private lemma sLow_mul_lemma {n : ℕ} {a b : Matrix (Fin n) (Fin n) K} (ha : IsLowUni a)
    (hb : IsLowUni b) : sLow (a * b) = sLow a + sLow b := by
  unfold sLow
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · rw [Matrix.mul_apply, Finset.sum_eq_add j ⟨j + 1, hj⟩]
    · rw [hb.2 j, ha.2 ⟨j + 1, hj⟩, mul_one, one_mul]
    · intro h
      have := congrArg Fin.val h
      simp at this
    · intro c _ hc
      by_cases hcj : c < j
      · rw [hb.1 hcj, mul_zero]
      · have hlt : (⟨j + 1, hj⟩ : Fin n) < c := by
          rw [Fin.lt_iff_val_lt_val]
          have h1 : (c : ℕ) ≠ j := fun e => hc.1 (Fin.ext e)
          have h2 : (c : ℕ) ≠ j + 1 := fun e => hc.2 (Fin.ext e)
          have h3 : (j : ℕ) ≤ c := by
            have := not_lt.1 hcj
            exact this
          show (j : ℕ) + 1 < c
          omega
        rw [ha.1 hlt, zero_mul]
    · simp
    · simp
  · simp

private lemma sUp_mul_lemma {n : ℕ} {a b : Matrix (Fin n) (Fin n) K} (ha : IsUpUni a)
    (hb : IsUpUni b) : sUp (a * b) = sUp a + sUp b := by
  unfold sUp
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · rw [Matrix.mul_apply, Finset.sum_eq_add j ⟨j + 1, hj⟩]
    · rw [ha.2 j, hb.2 ⟨j + 1, hj⟩, mul_one, one_mul, add_comm]
    · intro h
      have := congrArg Fin.val h
      simp at this
    · intro c _ hc
      by_cases hcj : c < j
      · rw [ha.1 hcj, zero_mul]
      · have hlt : (⟨j + 1, hj⟩ : Fin n) < c := by
          rw [Fin.lt_iff_val_lt_val]
          have h1 : (c : ℕ) ≠ j := fun e => hc.1 (Fin.ext e)
          have h2 : (c : ℕ) ≠ j + 1 := fun e => hc.2 (Fin.ext e)
          have h3 : (j : ℕ) ≤ c := by
            have := not_lt.1 hcj
            exact this
          show (j : ℕ) + 1 < c
          omega
        rw [hb.1 hlt, mul_zero]
    · simp
    · simp
  · simp

private lemma sLow_mem_lemma {n : ℕ} {x : Matrix (Fin n) (Fin n) K} (hx : IsInt R x) : sLow x ∈ R := by
  unfold sLow
  exact sum_mem fun j _ => by
    split_ifs
    exacts [hx _ _, zero_mem _]

private lemma sUp_mem_lemma {n : ℕ} {x : Matrix (Fin n) (Fin n) K} (hx : IsInt R x) : sUp x ∈ R := by
  unfold sUp
  exact sum_mem fun j _ => by
    split_ifs
    exacts [hx _ _, zero_mem _]

theorem term_inv (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) (w : Point K) {n' : ℕ}
    (Z' : Matrix (Fin n') (Fin n') K) (p p₁ : lowW K w.1 w.2 × upUniG K w.1.sum)
    (hp : toCos R p = toCos R p₁) :
    Fz R Z' (orbZ w p) * phase ψ p = Fz R Z' (orbZ w p₁) * phase ψ p₁ := by
  simp only [toCos, Prod.mk.injEq] at hp
  obtain ⟨hq1, hq2⟩ := hp
  obtain ⟨k, hk, e1⟩ := (sec_right_eq _ _ _).1 hq1
  rw [QuotientGroup.eq] at hq2
  set m := p.2⁻¹ * p₁.2 with hm
  have e2 : p₁.2 = p.2 * m := by rw [hm, mul_inv_cancel_left]
  have hk1 : IsLowUni (sec_m k) := k.2.1
  have hk2 : IsInt R (sec_m k) := hk.1
  have hm1 : IsUpUni (sec_m m) := m.2
  have hm2 : IsInt R (sec_m m) := hq2.1
  have eo : orbZ w p₁ = sec_m k * orbZ w p * sec_m m := by
    unfold orbZ
    rw [e1, e2]
    simp only [Subgroup.coe_mul, Units.val_mul, sec_m, Matrix.mul_assoc]
  have ep : phase ψ p₁ = phase ψ p * ψ (sLow (sec_m k) + sUp (sec_m m)) := by
    unfold phase
    rw [e1, e2]
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [sLow_mul_lemma hk1 p.1.2.1, sUp_mul_lemma p.2.2 hm1, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  have h1 : ψ (sLow (sec_m k) + sUp (sec_m m)) = 1 :=
    hψ _ (add_mem (sLow_mem_lemma R hk2) (sUp_mem_lemma R hm2))
  rw [eo, ep, h1, mul_one, Fz_uni R Z' _ _ _ hk1 hk2 hm1 hm2]

theorem Fz_cast {a s N n' : ℕ} (hN : N = a + s) (Z' : Matrix (Fin n') (Fin n') K)
    (Z : Matrix (Fin a) (Fin a) K) (X : Matrix (Fin s) (Fin a) K) (Y : Matrix (Fin a) (Fin s) K)
    (G : Matrix (Fin s) (Fin s) K) :
    Fz R Z' (bigZ hN Z X Y G) = Fz R Z' (bigZ rfl Z X Y G) := by
  subst hN
  rfl

theorem bbZ_eq (ψ : AddChar K ℂ) (w : Point K) {n' : ℕ} (Z' : Matrix (Fin n') (Fin n') K) :
    bbZ R ψ w Z' = ∑ᶠ q : Cos R w, Fz R Z' (orbZ w (rep R q)) * phase ψ (rep R q) := rfl

include hW in
theorem sum_identity [TopologicalSpace K] [IsTopologicalRing K] (ψ : AddChar K ℂ)
    (hD : LocalDatum K R ψ) {n' : ℕ} (Z' : Matrix (Fin n') (Fin n') K) :
    bbZ R ψ w Z' = omPhi R ψ g (PhiH R ψ h Z') := by
  have hψ : ∀ r ∈ R, ψ r = 1 := fun r hr => A6x4.psi_one hD hr
  set T : Cos R w → ℂ := fun q => Fz R Z' (orbZ w (rep R q)) * phase ψ (rep R q) with hT
  have hfin : (Function.support T).Finite := by
    refine (integral_points_finite K R ψ hD w).subset fun q hq => ?_
    by_contra hc
    apply hq
    have hc' : ¬ IsInt R (orbZ w (rep R q)) := hc
    simp only [hT, Fz, if_neg hc', zero_mul]
  let β : Par R h g → Cos R w := fun t => toCos R (sigma R hN hW t)
  have hβ : Function.Bijective β := sigma_bij R hN hW
  let e : Cos R g × (Cos R h × Matrix (Fin g.1.sum) (Fin h.1.sum) (KR R) ×
      Matrix (Fin h.1.sum) (Fin g.1.sum) (KR R)) ≃ Par R h g :=
    { toFun := fun x => ((x.2.1, x.1), x.2.2)
      invFun := fun t => (t.1.2, (t.1.1, t.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hβe : Function.Bijective (β ∘ e) := hβ.comp e.bijective
  have hfin2 : (Function.support (T ∘ (β ∘ e))).Finite := by
    rw [Function.support_comp_eq_preimage]
    exact hfin.preimage hβe.injective.injOn
  rw [bbZ_eq]
  rw [← finsum_eq_of_bijective (β ∘ e) hβe (fun x => rfl : ∀ x, (T ∘ (β ∘ e)) x = T ((β ∘ e) x))]
  rw [finsum_curry _ hfin2]
  unfold omPhi
  refine finsum_congr fun q => ?_
  unfold PhiH
  rw [mul_comm, ← smul_eq_mul, smul_finsum]
  refine finsum_congr fun τ => ?_
  show T (toCos R (sigma R hN hW ((τ.1, q), τ.2))) = _
  rw [hT]
  show Fz R Z' (orbZ w (rep R (toCos R (sigma R hN hW ((τ.1, q), τ.2))))) *
    phase ψ (rep R (toCos R (sigma R hN hW ((τ.1, q), τ.2)))) = _
  rw [term_inv R ψ hψ w Z' _ (sigma R hN hW ((τ.1, q), τ.2)) (A5x8.inv_toCos_rep R _)]
  unfold sigma
  rw [orbZ_J, phase_J, Fz_cast]
  show Fz R Z' (bigZ rfl (orbZ h (rep R τ.1)) (outM R τ.2.1) (outM R τ.2.2) (orbZ g (rep R q))) *
    (phase ψ (rep R τ.1) * ψ (cornL (outM R τ.2.1) + cornU (outM R τ.2.2)) * phase ψ (rep R q)) = _
  rw [smul_eq_mul]
  ring

end Sum

section Fin
variable {K : Type} [CommRing K] (R : Subring K)

theorem bigZ_det {a s N : ℕ} (hN : N = a + s) (Z : Matrix (Fin a) (Fin a) K)
    (X : Matrix (Fin s) (Fin a) K) (Y : Matrix (Fin a) (Fin s) K) (G : Matrix (Fin s) (Fin s) K) :
    (bigZ hN Z X Y G).det = Z.det * G.det := by
  have e : bigZ hN Z X Y G = blkM hN 1 0 X 1 * blkM hN Z 0 0 G * blkM hN 1 Y 0 1 := by
    unfold bigZ
    rw [blkM_mul, blkM_mul]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [e, Matrix.det_mul, Matrix.det_mul, blkM_det_low, blkM_det_low, blkM_det_up]
  simp

theorem bigZ_add {a s N : ℕ} (hN : N = a + s) (Z : Matrix (Fin a) (Fin a) K)
    (X : Matrix (Fin s) (Fin a) K) (Y : Matrix (Fin a) (Fin s) K) (G E : Matrix (Fin s) (Fin s) K) :
    bigZ hN Z X Y (G + E) = bigZ hN Z X Y G + blkM hN 0 0 0 E := by
  unfold bigZ
  rw [blkM_add]
  simp [add_assoc]

theorem mem_mulR {a x : K} : x ∈ mulR R a ↔ ∃ r ∈ R, x = a * r := by
  unfold mulR
  rw [AddSubgroup.mem_map]
  constructor <;> rintro ⟨r, hr, rfl⟩ <;> exact ⟨r, hr, rfl⟩

theorem PhiH_const (ψ : AddChar K ℂ) (h : Point K) {n' : ℕ} (Z' : Matrix (Fin n') (Fin n') K)
    (ϖ : K) (hϖ : ϖ ∈ R) (hu : ∀ r ∈ R, ∃ y ∈ R, (1 + ϖ * r) * y = 1) (k j : ℕ)
    (hj : ϖ ^ j * (pt h.1 h.2).det ^ 2 ∈ R) (s : ℕ) (G E : Matrix (Fin s) (Fin s) K) (c : K)
    (hc : G.det * c = 1) (hck : ϖ ^ k * c ∈ R)
    (hE : ∀ i l, ∃ r ∈ R, E i l = (pt h.1 h.2).det ^ 2 * ϖ ^ (2 * k + 1 + j) * r) :
    PhiH R ψ h Z' s (G + E) = PhiH R ψ h Z' s G := by
  have hdpt := pt_unit_lemma_5 h.1 h.2
  have hdG : IsUnit G.det := ⟨⟨G.det, c, hc, by rw [mul_comm]; exact hc⟩, rfl⟩
  unfold PhiH
  refine finsum_congr fun τ => ?_
  congr 1
  rw [bigZ_add]
  have hdZ : (orbZ h (rep R τ.1)).det = (pt h.1 h.2).det := by
    unfold orbZ
    rw [Matrix.det_mul, Matrix.det_mul, isLowUni_det K (rep R τ.1).1.2.1, isUpUni_det K (rep R τ.1).2.2]
    ring
  have hdet : (bigZ rfl (orbZ h (rep R τ.1)) (outM R τ.2.1) (outM R τ.2.2) G).det =
      (pt h.1 h.2).det * G.det := by
    rw [bigZ_det, hdZ]
  have hEm : ∀ i l, E i l ∈ R := by
    intro i l
    obtain ⟨r, hr, e⟩ := hE i l
    rw [e, show (pt h.1 h.2).det ^ 2 * ϖ ^ (2 * k + 1 + j) * r =
      ϖ ^ j * (pt h.1 h.2).det ^ 2 * ϖ ^ (2 * k + 1) * r by ring]
    exact R.mul_mem (R.mul_mem hj (R.pow_mem hϖ _)) hr
  apply Fz_perturb R ϖ hϖ hu Z'
  · rw [hdet]
    exact hdpt.mul hdG
  · exact (blkM_isInt rfl 0 0 0 E R).2 ⟨by intro i l; simp, by intro i l; simp, by intro i l; simp, hEm⟩
  · intro x y
    rw [hdet]
    obtain ⟨p, rfl⟩ := (eN (rfl : h.1.sum + s = h.1.sum + s)).surjective x
    obtain ⟨q, rfl⟩ := (eN (rfl : h.1.sum + s = h.1.sum + s)).surjective y
    rcases p with p | p <;> rcases q with q | q
    · exact ⟨0, R.zero_mem, by simp [blkM_ll]⟩
    · exact ⟨0, R.zero_mem, by simp [blkM_lr]⟩
    · exact ⟨0, R.zero_mem, by simp [blkM_rl]⟩
    · obtain ⟨r, hr, e⟩ := hE p q
      refine ⟨ϖ ^ j * (ϖ ^ k * c) ^ 2 * r,
        R.mul_mem (R.mul_mem (R.pow_mem hϖ _) (R.pow_mem hck _)) hr, ?_⟩
      rw [blkM_rr, e]
      linear_combination (-((pt h.1 h.2).det ^ 2 * ϖ ^ (2 * k + 1 + j) * r * (G.det * c + 1))) * hc

end Fin

end Formalism.FourierDecayAlt.P.TwoBlockPoint

namespace Formalism.FourierDecayAlt.P

open TwoBlockPoint in
theorem head_reduction_lemma : Formalism.FourierDecayAlt.A6.HeadReduction := by
  intro K _ _ _ R ψ hD hn m h Q hQc hQu
  obtain ⟨ϖ, hϖR, hϖK, hu, hbd⟩ := top_main R ψ hD hn
  obtain ⟨k, hk⟩ := hbd Q hQc hQu
  obtain ⟨j, hj⟩ := hϖK ((pt h.1 h.2).det ^ 2)
  have hψ : ∀ r ∈ R, ψ r = 1 := fun r hr => by simpa using (hD.selfDual 1).2 R.one_mem r hr
  have hdpt := pt_unit_lemma_5 h.1 h.2
  have hu0inv : ((hdpt.unit⁻¹ : Kˣ) : K) = Ring.inverse (pt h.1 h.2).det := by
    rw [← Ring.inverse_unit, IsUnit.unit_spec]
  have hlat : ∀ u : Kˣ, IsLat (mulR R (u : K)) := by
    intro u
    have e : ((mulR R (u : K)) : Set K) = (fun x => ((u⁻¹ : Kˣ) : K) * x) ⁻¹' (R : Set K) := by
      unfold mulR
      rw [AddSubgroup.coe_map, AddMonoidHom.coe_mulLeft]
      refine congrFun (Set.image_eq_preimage_of_inverse (fun x => ?_) (fun x => ?_)) _
      · show ((u⁻¹ : Kˣ) : K) * ((u : K) * x) = x
        rw [← mul_assoc, Units.inv_mul, one_mul]
      · show (u : K) * (((u⁻¹ : Kˣ) : K) * x) = x
        rw [← mul_assoc, Units.mul_inv, one_mul]
    refine ⟨?_, ?_⟩
    · rw [e]
      exact hD.isOpen.preimage (continuous_mul_left _)
    · unfold mulR
      rw [AddSubgroup.coe_map, AddMonoidHom.coe_mulLeft]
      exact hD.isCompact.image (continuous_mul_left _)
  refine ⟨mulR R ((hdpt.unit⁻¹ : Kˣ) : K), mulR R ((hdpt.unit ^ 2 * ϖ ^ (2 * k + 1 + j) : Kˣ) : K),
    hlat _, hlat _, fun n' Z' => ⟨fun n => PhiH R ψ h Z' n, ?_,
      fun t c => sum_identity R (two_block_point_size_sum h m t c) (two_block_point_block_matrix h m t c) ψ hD Z',
      fun z => sum_identity R (add_sum h (m + 1) z) (add_blk h (m + 1) z) ψ hD Z'⟩⟩
  unfold PhiHyp
  refine ⟨fun Z a b ha hai hb hbi => PhiH_inv R ψ hψ h Z' (m + 1) Z a b ha hai hb hbi,
    fun Z hne i l => ?_, fun Z Y hZ hY => ?_⟩
  · obtain ⟨r, hr, e⟩ := PhiH_supp R ψ h Z' (m + 1) Z hne i l
    refine (mem_mulR R).2 ⟨r, hr, ?_⟩
    rw [e, hu0inv]
  · have hE : ∀ i l, ∃ r ∈ R, Y i l = (pt h.1 h.2).det ^ 2 * (ϖ : K) ^ (2 * k + 1 + j) * r := by
      intro i l
      obtain ⟨r, hr, e⟩ := (mem_mulR R).1 (hY i l)
      refine ⟨r, hr, ?_⟩
      rw [e, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    rcases hZ with hZ | hZ
    · exact PhiH_const R ψ h Z' (ϖ : K) hϖR hu k j hj (m + 1) Z Y (Ring.inverse Z.det)
        (Ring.mul_inverse_cancel _ (hQu _ hZ)) (hk _ hZ) hE
    · refine PhiH_const R ψ h Z' (ϖ : K) hϖR hu k j hj (m + 1) Z Y (-Ring.inverse (-Z.det)) ?_ ?_ hE
      · rw [mul_neg, ← neg_mul, Ring.mul_inverse_cancel _ (hQu _ hZ)]
      · rw [mul_neg]
        exact R.neg_mem (hk _ hZ)

end Formalism.FourierDecayAlt.P
