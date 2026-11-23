import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne

namespace GlobalTheory.PsChar

open Matrix

theorem det_succ_eq_sub_sum_updateRow {A : Type*} [CommRing A] {m : ℕ} (N : Matrix (Fin (m + 1)) (Fin (m + 1)) A) :
    N.det = N 0 0 * (N.submatrix Fin.succ Fin.succ).det -
      ∑ c : Fin m, N c.succ 0 * ((N.submatrix Fin.succ Fin.succ).updateRow c (fun b => N 0 b.succ)).det := by
  rw [Matrix.det_apply', Finset.univ_perm_fin_succ, Finset.sum_map, Fintype.sum_prod_type, Fin.sum_univ_succ,
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · rw [Matrix.det_apply', Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp [Fin.prod_univ_succ, Equiv.Perm.decomposeFin.symm_sign]
    ring
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.det_apply', Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h : ∀ i : Fin m, N (Equiv.swap 0 c.succ (e i).succ) i.succ =
        (N.submatrix Fin.succ Fin.succ).updateRow c (fun b => N 0 b.succ) (e i) i := by
      intro i
      by_cases hc : e i = c
      · simp [hc]
      · rw [Matrix.updateRow_ne hc, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
          (fun h => hc (Fin.succ_injective _ h))]
        rfl
    simp [Fin.prod_univ_succ, Equiv.Perm.decomposeFin.symm_sign, h]
    ring

theorem alt_trace_eq_sum_det {M A : Type*} [Monoid M] [CommRing A] {n : ℕ} (r : M →* Matrix (Fin n) (Fin n) A) :
    ∀ (m : ℕ) (x : Fin m → M), alt (fun g => (r g).trace) m x =
      ∑ i : Fin m → Fin n, (Matrix.of fun a b => r (x a) (i b) (i a)).det
  | 0, x => by simp [alt]
  | m + 1, x => by
    rw [alt, ← (Fin.consEquiv (fun _ : Fin (m + 1) => Fin n)).sum_comp, Fintype.sum_prod_type]
    simp only [alt_trace_eq_sum_det r m, det_succ_eq_sub_sum_updateRow, Finset.sum_sub_distrib]
    congr 1
    · rw [Matrix.trace, Finset.sum_mul_sum]
      rfl
    · rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      have h1 : (Matrix.of fun a b => r (Function.update (Fin.tail x) c (x 0 * Fin.tail x c) a) (i b) (i a)) =
          (Matrix.of fun a b => r (x a.succ) (i b) (i a)).updateRow c
            (∑ j : Fin n, r (x c.succ) j (i c) • fun b => r (x 0) (i b) j) := by
        ext a b
        by_cases h : a = c
        · subst h
          simp [Fin.tail, Matrix.mul_apply, mul_comm]
        · simp [Fin.tail, h]
      rw [h1]
      have h2 : ∀ (P : Matrix (Fin m) (Fin m) A) (s : Finset (Fin n)) (w : Fin n → A) (v : Fin n → Fin m → A),
          (P.updateRow c (∑ j ∈ s, w j • v j)).det = ∑ j ∈ s, w j * (P.updateRow c (v j)).det := by
        intro P s w v
        induction s using Finset.induction_on with
        | empty =>
          simp only [Finset.sum_empty]
          exact Matrix.det_eq_zero_of_row_eq_zero c (by simp)
        | insert j s hj ih =>
          rw [Finset.sum_insert hj, Finset.sum_insert hj, Matrix.det_updateRow_add, ih, Matrix.det_updateRow_smul]
      rw [h2]
      rfl

theorem isPsChar_trace (M A : Type) [Monoid M] [CommRing A] (n : ℕ) (r : M →* Matrix (Fin n) (Fin n) A) :
    IsPsChar n (fun g => (r g).trace) where
  one := by simp
  comm x y := by simp only [map_mul]; exact Matrix.trace_mul_comm _ _
  alt_eq_zero x := by
    rw [alt_trace_eq_sum_det]
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨b, b', hne, hb⟩ := Fintype.exists_ne_map_eq_of_card_lt i (by simp)
    exact Matrix.det_zero_of_column_eq hne (fun a => by simp [hb])

end GlobalTheory.PsChar
