import Formalism.ThetaLogCoordinates.DualWeylCoordinates.StripDataTensorColumnFamilies

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

def qs_sg (A : Finset (Fin n)) (m : Fin n) : ℤ := (-1) ^ (A.filter (m < ·)).card

def qs_mn {R : Type*} [CommRing R] (g : Matrix (Fin n) (Fin n) R) (J I : Finset (Fin n)) : R :=
  if h : J.card = I.card then
    Matrix.det (Matrix.of fun a b : Fin I.card => g (J.orderEmbOfFin h a) (I.orderEmbOfFin rfl b)) else 0

variable {R : Type*} [CommRing R] (g : Matrix (Fin n) (Fin n) R)

lemma qs_mn_eq {h : ℕ} (J I : Finset (Fin n)) (hJ : J.card = h) (hI : I.card = h) :
    qs_mn g J I = Matrix.det (Matrix.of fun a b : Fin h => g (J.orderEmbOfFin hJ a) (I.orderEmbOfFin hI b)) := by
  subst hI; rw [qs_mn, dif_pos hJ]

lemma qs_mn_ne {J I : Finset (Fin n)} (h : J.card ≠ I.card) : qs_mn g J I = 0 := dif_neg h

lemma qs_mn_transpose (J I : Finset (Fin n)) : qs_mn g.transpose J I = qs_mn g I J := by
  by_cases h : J.card = I.card
  · rw [qs_mn_eq _ J I h rfl, qs_mn_eq _ I J rfl h, ← Matrix.det_transpose]; rfl
  · rw [qs_mn_ne _ h, qs_mn_ne _ (Ne.symm h)]

lemma qs_oe_succAbove {h : ℕ} (s : Finset (Fin n)) (hs : s.card = h + 1) (j : Fin (h + 1))
    (hs' : (s.erase (s.orderEmbOfFin hs j)).card = h) (i : Fin h) :
    s.orderEmbOfFin hs (j.succAbove i) = (s.erase (s.orderEmbOfFin hs j)).orderEmbOfFin hs' i := by
  have := Finset.orderEmbOfFin_unique hs' (f := fun i => s.orderEmbOfFin hs (j.succAbove i))
    (fun x => Finset.mem_erase.2 ⟨(s.orderEmbOfFin hs).injective.ne (Fin.succAbove_ne j x),
      Finset.orderEmbOfFin_mem _ _ _⟩)
    ((s.orderEmbOfFin hs).strictMono.comp (Fin.strictMono_succAbove j))
  exact congrFun this i

lemma qs_card_gt {h : ℕ} (s : Finset (Fin n)) (hs : s.card = h + 1) (j : Fin (h + 1)) :
    ((s.erase (s.orderEmbOfFin hs j)).filter (s.orderEmbOfFin hs j < ·)).card = h - j := by
  have : (s.erase (s.orderEmbOfFin hs j)).filter (s.orderEmbOfFin hs j < ·) =
      (Finset.Ioi j).map (s.orderEmbOfFin hs).toEmbedding := by
    ext x
    simp only [mem_filter, mem_erase, mem_map, mem_Ioi, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨⟨_, hx⟩, hlt⟩
      have hx' : x ∈ Set.range (s.orderEmbOfFin hs) := by rw [Finset.range_orderEmbOfFin]; exact hx
      obtain ⟨i, rfl⟩ := hx'
      exact ⟨i, (s.orderEmbOfFin hs).lt_iff_lt.1 hlt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨((s.orderEmbOfFin hs).lt_iff_lt.2 hi).ne', Finset.orderEmbOfFin_mem _ _ _⟩,
        (s.orderEmbOfFin hs).lt_iff_lt.2 hi⟩
  rw [this, card_map, Fin.card_Ioi]; omega

lemma qs_sum_oe {M : Type*} [AddCommMonoid M] {h : ℕ} (I : Finset (Fin n)) (hI : I.card = h) (f : Fin n → M) :
    ∑ m ∈ I, f m = ∑ j : Fin h, f (I.orderEmbOfFin hI j) := by
  conv_lhs => rw [← Finset.map_orderEmbOfFin_univ I hI]
  rw [Finset.sum_map]; rfl

lemma qs_lap_row {h : ℕ} (r : Fin (h + 1) → Fin n) (p : Fin (h + 1)) (I : Finset (Fin n)) (hI : I.card = h + 1)
    (A : Finset (Fin n)) (hA : A.card = h) (hr : ∀ i, r (p.succAbove i) = A.orderEmbOfFin hA i) :
    ∑ m ∈ I, ((qs_sg (I.erase m) m : ℤ) : R) * qs_mn g A (I.erase m) * g (r p) m =
      (-1) ^ (h - (p : ℕ)) * Matrix.det (Matrix.of fun a b : Fin (h + 1) => g (r a) (I.orderEmbOfFin hI b)) := by
  rw [Matrix.det_succ_row _ p, Finset.mul_sum, qs_sum_oe I hI]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : (I.erase (I.orderEmbOfFin hI j)).card = h := by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), hI]; rfl
  rw [qs_mn_eq g A _ hA hc, qs_sg, qs_card_gt I hI j]
  have hM : (Matrix.of fun a b : Fin (h + 1) => g (r a) (I.orderEmbOfFin hI b)).submatrix p.succAbove j.succAbove =
      Matrix.of fun a b : Fin h => g (A.orderEmbOfFin hA a) ((I.erase (I.orderEmbOfFin hI j)).orderEmbOfFin hc b) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.of_apply]
    rw [hr, qs_oe_succAbove I hI j hc]
  rw [hM]
  have hs : ((-1 : R)) ^ (h - (j : ℕ)) = (-1) ^ (h - (p : ℕ)) * (-1) ^ ((p : ℕ) + (j : ℕ)) := by
    rw [← pow_add]
    have hj := j.2; have hp := p.2
    have : h - (p : ℕ) + ((p : ℕ) + (j : ℕ)) = (h - (j : ℕ)) + 2 * (j : ℕ) := by omega
    rw [this, pow_add, pow_mul]; simp
  push_cast
  rw [hs]
  simp only [Matrix.of_apply]
  ring

theorem qs_laplace (A I : Finset (Fin n)) (k : Fin n) :
    ∑ m ∈ I, ((qs_sg (I.erase m) m : ℤ) : R) * qs_mn g A (I.erase m) * g k m =
      if k ∈ A then 0 else ((qs_sg A k : ℤ) : R) * qs_mn g (insert k A) I := by
  by_cases hc : I.card = A.card + 1
  · split_ifs with hk
    ·
      have hk' : k ∈ Set.range (A.orderEmbOfFin rfl) := by rw [Finset.range_orderEmbOfFin]; exact hk
      obtain ⟨q, hq⟩ := hk'
      have := qs_lap_row g (Fin.cons k (A.orderEmbOfFin rfl)) 0 I hc A rfl (fun i => by simp)
      simp only [Fin.cons_zero] at this
      rw [this, Matrix.det_zero_of_row_eq (i := 0) (j := q.succ) (Fin.succ_ne_zero q).symm, mul_zero]
      ext b; simp [hq]
    · have hs : (insert k A).card = A.card + 1 := Finset.card_insert_of_notMem hk
      have hk' : k ∈ Set.range ((insert k A).orderEmbOfFin hs) := by
        rw [Finset.range_orderEmbOfFin]; simp
      obtain ⟨p, hp⟩ := hk'
      have he : (insert k A).erase ((insert k A).orderEmbOfFin hs p) = A := by
        rw [hp, Finset.erase_insert hk]
      have hAc : ((insert k A).erase ((insert k A).orderEmbOfFin hs p)).card = A.card := by rw [he]
      have := qs_lap_row g ((insert k A).orderEmbOfFin hs) p I hc _ hAc
        (fun i => qs_oe_succAbove _ hs p hAc i)
      have h2 := qs_card_gt (insert k A) hs p
      rw [he, hp] at this h2
      rw [this, qs_mn_eq g _ _ hs hc, qs_sg, h2]
      push_cast; rfl
  · have h1 : ∀ m ∈ I, qs_mn g A (I.erase m) = 0 := fun m hm => qs_mn_ne g (by
      rw [Finset.card_erase_of_mem hm]
      have := Finset.card_pos.2 ⟨m, hm⟩
      omega)
    rw [Finset.sum_eq_zero (fun m hm => by rw [h1 m hm]; simp)]
    split_ifs with hk
    · rfl
    · rw [qs_mn_ne g (by rw [Finset.card_insert_of_notMem hk]; omega), mul_zero]

theorem qs_laplace_col (A I : Finset (Fin n)) (m : Fin n) :
    ∑ k ∈ A, ((qs_sg (A.erase k) k : ℤ) : R) * qs_mn g (A.erase k) I * g k m =
      if m ∈ I then 0 else ((qs_sg I m : ℤ) : R) * qs_mn g A (insert m I) := by
  have := qs_laplace g.transpose I A m
  simpa only [qs_mn_transpose, Matrix.transpose_apply] using this

end Formalism.InvariantFactorPaths.ColumnFamilies
