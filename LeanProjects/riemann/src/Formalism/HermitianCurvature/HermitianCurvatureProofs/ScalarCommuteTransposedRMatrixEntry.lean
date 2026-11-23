import Formalism.HermitianCurvature.StatementWd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EntryCommuteTransposedRMatrix

namespace Formalism.FourierDecayAlt.P.Wd7

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd

section Base

variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]

theorem cond_iff (a : S) (i j : Fin 2) (x y : Ix S) :
    (x a = i ∧ y a = j ∧ ∀ b, b ≠ a → x b = y b) ↔ (x a = i ∧ y = Function.update x a j) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_⟩
    funext b
    by_cases hb : b = a
    · subst hb; simp [h2]
    · simp [Function.update_of_ne hb, h3 b hb]
  · rintro ⟨h1, rfl⟩
    refine ⟨h1, by simp, ?_⟩
    intro b hb
    simp [Function.update_of_ne hb]

theorem cond_iff' (a : S) (i j : Fin 2) (x y : Ix S) :
    (x a = i ∧ y a = j ∧ ∀ b, b ≠ a → x b = y b) ↔ (y a = j ∧ x = Function.update y a i) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h2, ?_⟩
    funext b
    by_cases hb : b = a
    · subst hb; simp [h1]
    · simp [Function.update_of_ne hb, h3 b hb]
  · rintro ⟨h1, rfl⟩
    refine ⟨by simp, h1, ?_⟩
    intro b hb
    simp [Function.update_of_ne hb]

theorem eU_apply (a : S) (i j : Fin 2) (x y : Ix S) :
    (eU a i j : SlopeTestRemainingChoices S A) x y = if x a = i ∧ y = Function.update x a j then 1 else 0 := by
  unfold eU
  simp only [Matrix.of_apply]
  exact if_congr (cond_iff a i j x y) rfl rfl

theorem eU_apply' (a : S) (i j : Fin 2) (x y : Ix S) :
    (eU a i j : SlopeTestRemainingChoices S A) x y = if y a = j ∧ x = Function.update y a i then 1 else 0 := by
  unfold eU
  simp only [Matrix.of_apply]
  exact if_congr (cond_iff' a i j x y) rfl rfl

theorem eU_mul_apply (a : S) (i j : Fin 2) (B : SlopeTestRemainingChoices S A) (x y : Ix S) :
    ((eU a i j : SlopeTestRemainingChoices S A) * B) x y = if x a = i then B (Function.update x a j) y else 0 := by
  rw [Matrix.mul_apply]
  simp only [eU_apply]
  by_cases h : x a = i
  · simp [h]
  · simp [h]

theorem mul_eU_apply (a : S) (i j : Fin 2) (B : SlopeTestRemainingChoices S A) (x y : Ix S) :
    (B * (eU a i j : SlopeTestRemainingChoices S A)) x y = if y a = j then B x (Function.update y a i) else 0 := by
  rw [Matrix.mul_apply]
  simp only [eU_apply']
  by_cases h : y a = j
  · simp [h]
  · simp [h]

theorem eU_mul_eU (a : S) (i j k l : Fin 2) :
    (eU a i j : SlopeTestRemainingChoices S A) * eU a k l = if j = k then eU a i l else 0 := by
  ext x y
  rw [eU_mul_apply, eU_apply]
  by_cases hjk : j = k
  · subst hjk
    simp only [Function.update_self, Function.update_idem, true_and, if_true]
    rw [eU_apply]
    by_cases h : x a = i <;> simp [h]
  · simp [hjk]

theorem eU_comm_of_ne {a c : S} (hc : c ≠ a) (i j k l : Fin 2) :
    Commute (eU c i j : SlopeTestRemainingChoices S A) (eU a k l) := by
  show (eU c i j : SlopeTestRemainingChoices S A) * eU a k l = eU a k l * eU c i j
  ext x y
  rw [eU_mul_apply, eU_mul_apply, eU_apply, eU_apply]
  rw [Function.update_of_ne (Ne.symm hc), Function.update_of_ne hc, Function.update_comm hc]
  by_cases h1 : x c = i <;> by_cases h2 : x a = k <;> simp [h1, h2]

theorem star_eU [StarRing A] (a : S) (i j : Fin 2) :
    star (eU a i j : SlopeTestRemainingChoices S A) = eU a j i := by
  ext x y
  rw [Matrix.star_apply, eU_apply, eU_apply']
  by_cases h : y a = i ∧ x = Function.update y a j <;> simp [h]

theorem ins_mul (a : S) (M N : M2 (SlopeTestRemainingChoices S A)) (hM : FreeOf2 a M) :
    ins a (M * N) = ins a M * ins a N := by
  unfold ins
  have key : ∀ i j k l : Fin 2, (eU a i j * M i j) * ((eU a k l : SlopeTestRemainingChoices S A) * N k l) =
      if j = k then eU a i l * (M i j * N k l) else 0 := by
    intro i j k l
    have h := (hM i j k l).eq
    calc (eU a i j * M i j) * ((eU a k l : SlopeTestRemainingChoices S A) * N k l)
        = eU a i j * (M i j * eU a k l) * N k l := by simp only [mul_assoc]
      _ = eU a i j * (eU a k l * M i j) * N k l := by rw [h]
      _ = (eU a i j * eU a k l) * (M i j * N k l) := by simp only [mul_assoc]
      _ = _ := by rw [eU_mul_eU]; split_ifs <;> simp
  simp only [Finset.sum_mul, Finset.mul_sum, key, Matrix.mul_apply]
  simp only [Fin.sum_univ_two]
  simp
  abel

theorem ins_star [StarRing A] (a : S) (M : M2 (SlopeTestRemainingChoices S A)) (hM : FreeOf2 a M) :
    star (ins a M) = ins a Mᴴ := by
  unfold ins
  have key : ∀ i j : Fin 2, star ((eU a i j : SlopeTestRemainingChoices S A) * M i j) = eU a j i * Mᴴ j i := by
    intro i j
    rw [star_mul, star_eU, Matrix.conjTranspose_apply]
    have h := (hM i j i j).star_star
    rw [star_eU] at h
    exact h.eq.symm
  simp only [star_sum, key]
  exact Finset.sum_comm

theorem ins_free {a c : S} (hc : c ≠ a) (M : M2 (SlopeTestRemainingChoices S A)) (hM : FreeOf2 c M) :
    FreeOf c (ins a M) := by
  intro i j
  unfold ins
  refine Commute.sum_right _ _ _ fun k _ => Commute.sum_right _ _ _ fun l _ => ?_
  exact (eU_comm_of_ne hc i j k l).mul_right (hM k l i j)

theorem ins_comm (a : S) (M : M2 (SlopeTestRemainingChoices S A)) (b : SlopeTestRemainingChoices S A) (hb : FreeOf a b)
    (hbM : ∀ i j, Commute b (M i j)) : Commute b (ins a M) := by
  unfold ins
  refine Commute.sum_right _ _ _ fun k _ => Commute.sum_right _ _ _ fun l _ => ?_
  exact (hb k l).symm.mul_right (hbM k l)

theorem insert_mul_diagScalar (a : S) (M : M2 (SlopeTestRemainingChoices S A)) (b : SlopeTestRemainingChoices S A) : ins a (M * d0 b) = ins a M * b := by
  unfold ins d0
  simp only [Matrix.mul_diagonal, Finset.sum_mul, mul_assoc]

theorem insert_diagScalar_mul_of_free (a : S) (M : M2 (SlopeTestRemainingChoices S A)) (b : SlopeTestRemainingChoices S A) (hb : FreeOf a b) :
    ins a (d0 b * M) = b * ins a M := by
  unfold ins d0
  simp only [Matrix.diagonal_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, (hb i j).eq, mul_assoc]

theorem io_mul_apply (x : A) (M : SlopeTestRemainingChoices S A) (z y : Ix S) : ((io x : SlopeTestRemainingChoices S A) * M) z y = x * M z y := by
  simp [io, Matrix.scalar_apply, Matrix.diagonal_mul]

theorem mul_io_apply (x : A) (M : SlopeTestRemainingChoices S A) (z y : Ix S) : (M * (io x : SlopeTestRemainingChoices S A)) z y = M z y * x := by
  simp [io, Matrix.scalar_apply, Matrix.mul_diagonal]

theorem io_apply (x : A) (z y : Ix S) : (io x : SlopeTestRemainingChoices S A) z y = if z = y then x else 0 := by
  simp [io, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem io_comm_eU (a : S) (i j : Fin 2) (x : A) : Commute (eU a i j : SlopeTestRemainingChoices S A) (io x) := by
  show (eU a i j : SlopeTestRemainingChoices S A) * io x = io x * eU a i j
  ext z y
  rw [io_mul_apply, mul_io_apply, eU_apply]
  split_ifs <;> simp

theorem io_comm_io {x y : A} (h : Commute x y) : Commute (io x : SlopeTestRemainingChoices S A) (io y) := by
  show (io x : SlopeTestRemainingChoices S A) * io y = io y * io x
  ext z z'
  rw [io_mul_apply, io_mul_apply, io_apply, io_apply]
  split_ifs
  · exact h.eq
  · simp

theorem free_apply_zero {a : S} {M : SlopeTestRemainingChoices S A} (hM : FreeOf a M) {z y : Ix S} (h : z a ≠ y a) :
    M z y = 0 := by
  have h1 := congrFun (congrFun (hM (z a) (z a)).eq z) y
  rw [eU_mul_apply, mul_eU_apply, if_pos rfl, if_neg (Ne.symm h), Function.update_eq_self] at h1
  exact h1

theorem free_one (a : S) : FreeOf a (1 : SlopeTestRemainingChoices S A) := fun _ _ => Commute.one_right _
theorem free_zero (a : S) : FreeOf a (0 : SlopeTestRemainingChoices S A) := fun _ _ => Commute.zero_right _
theorem free_mul {a : S} {x y : SlopeTestRemainingChoices S A} (hx : FreeOf a x) (hy : FreeOf a y) : FreeOf a (x * y) :=
  fun i j => (hx i j).mul_right (hy i j)
theorem free_add {a : S} {x y : SlopeTestRemainingChoices S A} (hx : FreeOf a x) (hy : FreeOf a y) : FreeOf a (x + y) :=
  fun i j => (hx i j).add_right (hy i j)
theorem free_sub {a : S} {x y : SlopeTestRemainingChoices S A} (hx : FreeOf a x) (hy : FreeOf a y) : FreeOf a (x - y) :=
  fun i j => (hx i j).sub_right (hy i j)
theorem free_io (a : S) (x : A) : FreeOf a (io x : SlopeTestRemainingChoices S A) := fun i j => io_comm_eU a i j x
theorem free_eU {a c : S} (hc : c ≠ a) (k l : Fin 2) : FreeOf c (eU a k l : SlopeTestRemainingChoices S A) :=
  fun i j => eU_comm_of_ne hc i j k l
theorem free_smul {K : Type} [Field K] [Algebra K A] {a : S} (k : K) {x : SlopeTestRemainingChoices S A} (hx : FreeOf a x) :
    FreeOf a (k • x) := fun i j => (hx i j).smul_right k

theorem freeOf2_mul {a : S} {M N : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 a M) (hN : FreeOf2 a N) :
    FreeOf2 a (M * N) := by
  intro i j
  rw [Matrix.mul_apply]
  intro k l
  exact Commute.sum_right _ _ _ fun m _ => (hM i m k l).mul_right (hN m j k l)

theorem freeOf2_one (a : S) : FreeOf2 a (1 : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact free_one a
  · exact free_zero a

theorem freeOf2_transpose {a : S} {M : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 a M) : FreeOf2 a Mᵀ :=
  fun i j => hM j i

theorem freeOf2_lift (a : S) (M : M2 A) : FreeOf2 a (lift0 M : M2 (SlopeTestRemainingChoices S A)) :=
  fun i j => free_io a (M i j)

end Base

section Words

variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem freeOf2_rmatrix {a c : S} (hc : c ≠ a) (D : K) : FreeOf2 c (Rh0 a D : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  have h : (Rh0 a D : M2 (SlopeTestRemainingChoices S A)) i j =
      (D - 1)⁻¹ • (D • (1 : M2 (SlopeTestRemainingChoices S A)) i j - eU a j i) := rfl
  rw [h]
  exact free_smul _ (free_sub (free_smul _ (freeOf2_one c i j)) (free_eU hc j i))

theorem freeOf2_rmatrix_transpose {a c : S} (hc : c ≠ a) (D : K) : FreeOf2 c (Rht0 a D : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  have h : (Rht0 a D : M2 (SlopeTestRemainingChoices S A)) i j =
      (D - 1)⁻¹ • (D • (1 : M2 (SlopeTestRemainingChoices S A)) i j - eU a i j) := rfl
  rw [h]
  exact free_smul _ (free_sub (free_smul _ (freeOf2_one c i j)) (free_eU hc i j))

theorem freeOf_positive_word_matrix {c : S} (w : List (Letter K S)) (hc : c ∉ w.map Letter.intersection_update_fsHerm_neg_one) (Y : K) :
    FreeOf2 c (Xp w Y : M2 (SlopeTestRemainingChoices S A)) := by
  induction w with
  | nil => exact freeOf2_one c
  | cons l w ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hc
    by_cases h : l.plus
    · simp only [Xp, h, if_true]
      exact freeOf2_mul (ih hc.2) (freeOf2_rmatrix hc.1 _)
    · simp only [Xp, h]
      exact ih hc.2

theorem freeOf_negative_word_matrix {c : S} (w : List (Letter K S)) (hc : c ∉ w.map Letter.intersection_update_fsHerm_neg_one) (Y : K) :
    FreeOf2 c (Xm w Y : M2 (SlopeTestRemainingChoices S A)) := by
  induction w with
  | nil => exact freeOf2_one c
  | cons l w ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hc
    by_cases h : l.plus
    · simp only [Xm, h, if_true]
      exact ih hc.2
    · simp only [Xm, h]
      exact freeOf2_mul (freeOf2_rmatrix_transpose hc.1 _) (ih hc.2)

theorem TTw_factor (QQ : K → M2 A) (w : List (Letter K S)) (Y : K) :
    TTw QQ w Y = Xm w Y * lift0 (QQ Y) * Xp w Y := by
  induction w with
  | nil => simp [TTw, Xm, Xp]
  | cons l w ih => by_cases h : l.plus <;> simp [TTw, Xm, Xp, h, ih, mul_assoc]

theorem freeOf_transfer_word_matrix {c : S} (QQ : K → M2 A) (w : List (Letter K S)) (hc : c ∉ w.map Letter.intersection_update_fsHerm_neg_one)
    (Y : K) : FreeOf2 c (TTw QQ w Y) := by
  rw [TTw_factor]
  exact freeOf2_mul (freeOf2_mul (freeOf_negative_word_matrix w hc Y) (freeOf2_lift c _)) (freeOf_positive_word_matrix w hc Y)

theorem free_RRw {c : S} (QQ : K → M2 A) (w : List (Letter K S)) (hc : c ∉ w.map Letter.intersection_update_fsHerm_neg_one) :
    FreeOf c (RRw QQ w) := by
  induction w with
  | nil => exact free_one c
  | cons l w ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hc
    simp only [RRw]
    refine free_mul (ih hc.2) (ins_free hc.1 _ ?_)
    split_ifs
    · exact freeOf_transfer_word_matrix QQ w hc.2 _
    · exact freeOf2_transpose (freeOf_transfer_word_matrix QQ w hc.2 _)

theorem smul_cancel (D : K) (hD : D ≠ 1) (x : A) : (D - 1)⁻¹ • (D • x - x) = x := by
  have h : D • x - x = (D - 1) • x := by rw [sub_smul, one_smul]
  rw [h, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hD), one_smul]

theorem Rh0_col (a : S) (D : K) (hD : D ≠ 1) (m : Fin 2) (z : Ix S) :
    (Rh0 a D m 0 : SlopeTestRemainingChoices S A) z e1 = if m = 0 ∧ z = e1 then 1 else 0 := by
  have h : (Rh0 a D m 0 : SlopeTestRemainingChoices S A) z e1 =
      (D - 1)⁻¹ • (D • ((1 : M2 (SlopeTestRemainingChoices S A)) m 0) z e1 - (eU a 0 m : SlopeTestRemainingChoices S A) z e1) := rfl
  have hu : Function.update (e1 : Ix S) a 0 = e1 := Function.update_eq_self a e1
  have he : (e1 : Ix S) a = 0 := rfl
  rw [h, eU_apply', Matrix.one_apply, he, hu]
  by_cases hm : m = 0
  · subst hm
    by_cases hz : z = e1
    · subst hz
      simp only [if_true, and_self, Matrix.one_apply_eq]
      exact smul_cancel D hD 1
    · simp [hz]
  · have hm' : ¬ (0 = m) := fun h => hm h.symm
    simp [hm, hm']

theorem mul_col (M N : M2 (SlopeTestRemainingChoices S A))
    (hN : ∀ (m : Fin 2) (z : Ix S), (N m 0) z e1 = if m = 0 ∧ z = e1 then 1 else 0)
    (k : Fin 2) (z : Ix S) : ((M * N) k 0) z e1 = (M k 0) z e1 := by
  rw [Matrix.mul_apply, Matrix.sum_apply]
  simp only [Matrix.mul_apply, hN]
  rw [Fin.sum_univ_two]
  simp

theorem Xp_fix (w : List (Letter K S)) (Y : K) (hr : Reg w Y) (k : Fin 2) (z : Ix S) :
    (Xp w Y k 0 : SlopeTestRemainingChoices S A) z e1 = if k = 0 ∧ z = e1 then 1 else 0 := by
  induction w generalizing k z with
  | nil =>
    simp only [Xp, Matrix.one_apply]
    by_cases hk : k = 0
    · simp [hk, Matrix.one_apply]
    · simp [hk]
  | cons l w ih =>
    have hr' : Reg w Y := fun l' hl' => hr l' (List.mem_cons_of_mem _ hl')
    by_cases h : l.plus
    · have hl : Y - l.pt ≠ 1 := by
        have := hr l List.mem_cons_self
        simpa [RegL, h] using this
      simp only [Xp, h, if_true]
      rw [mul_col _ _ (Rh0_col l.intersection_update_fsHerm_neg_one _ hl)]
      exact ih hr' k z
    · simp only [Xp, h]
      exact ih hr' k z

theorem Rht0_row (b : S) (d : K) (hd : d ≠ 1) (X : M2 (SlopeTestRemainingChoices S A)) (hX : FreeOf2 b X)
    (k : Fin 2) (z : Ix S) : ((Rht0 b d * X : M2 (SlopeTestRemainingChoices S A)) 0 k) z e1 = (X 0 k) z e1 := by
  have h : (Rht0 b d * X : M2 (SlopeTestRemainingChoices S A)) 0 k =
      (d - 1)⁻¹ • (d • X 0 k - (eU b 0 0 * X 0 k + eU b 0 1 * X 1 k)) := by
    unfold Rht0
    rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Q0,
      Matrix.of_apply]
  rw [h]
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, eU_mul_apply]
  have h1 : (X 1 k) (Function.update z b 1) e1 = 0 := by
    apply free_apply_zero (hX 1 k)
    simp [e1]
  by_cases hz : z b = 0
  · have hu : Function.update z b 0 = z := by rw [← hz]; exact Function.update_eq_self b z
    simp only [hz, if_true, h1, add_zero, hu]
    exact smul_cancel d hd _
  · have h0 : (X 0 k) z e1 = 0 := free_apply_zero (hX 0 k) hz
    simp [hz, h0]

theorem Xm_fix (w : List (Letter K S)) (Y : K) (hn : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) (hr : Reg w Y)
    (k : Fin 2) (z : Ix S) :
    (Xm w Y 0 k : SlopeTestRemainingChoices S A) z e1 = if k = 0 ∧ z = e1 then 1 else 0 := by
  induction w generalizing k z with
  | nil =>
    simp only [Xm, Matrix.one_apply]
    by_cases hk : k = 0
    · simp [hk, Matrix.one_apply]
    · have hk' : ¬ (0 = k) := fun h => hk h.symm
      simp [hk, hk']
  | cons l w ih =>
    have hr' : Reg w Y := fun l' hl' => hr l' (List.mem_cons_of_mem _ hl')
    simp only [List.map_cons, List.nodup_cons] at hn
    by_cases h : l.plus
    · simp only [Xm, h, if_true]
      exact ih hn.2 hr' k z
    · have hl : l.pt - Y ≠ 1 := by
        have := hr l List.mem_cons_self
        simpa [RegL, h] using this
      rw [show (Xm (l :: w) Y : M2 (SlopeTestRemainingChoices S A)) = Rht0 l.intersection_update_fsHerm_neg_one (l.pt - Y) * Xm w Y from by simp [Xm, h]]
      rw [Rht0_row l.intersection_update_fsHerm_neg_one _ hl _ (freeOf_negative_word_matrix w hn.1 Y)]
      exact ih hn.2 hr' k z

theorem TTw_corner (QQ : K → M2 A) (w : List (Letter K S)) (Y : K)
    (hn : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) (hr : Reg w Y) (z : Ix S) :
    (TTw QQ w Y 0 0) z e1 = if z = e1 then QQ Y 0 0 else 0 := by
  rw [TTw_factor, mul_col _ _ (Xp_fix w Y hr), Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Matrix.add_apply, lift0, Matrix.map_apply, mul_io_apply, Xm_fix w Y hn hr]
  by_cases hz : z = e1 <;> simp [hz]

theorem entry_ins (a : S) (R : SlopeTestRemainingChoices S A) (M : M2 (SlopeTestRemainingChoices S A)) (hR : FreeOf a R) (hM : FreeOf2 a M) :
    (R * ins a M) e1 e1 = (R * M 0 0) e1 e1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : z a = 0
  · congr 1
    unfold ins
    simp only [Fin.sum_univ_two, Matrix.add_apply, eU_mul_apply, hz, if_true]
    have hu : Function.update z a 0 = z := by rw [← hz]; exact Function.update_eq_self a z
    have h1 : ∀ i, (M i 1) (Function.update z a 1) e1 = 0 := fun i => by
      apply free_apply_zero (hM i 1)
      simp [e1]
    simp [hu, h1]
  · have h0 : R e1 z = 0 := free_apply_zero hR (fun h => hz h.symm)
    rw [h0, zero_mul, zero_mul]

theorem good_cons {l : Letter K S} {w : List (Letter K S)} (h : Good (l :: w)) :
    Good w ∧ l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one ∧ star l.pt = l.pt ∧ Reg w l.pt := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [List.map_cons, List.nodup_cons] at h1
  rw [List.pairwise_cons] at h3
  exact ⟨⟨h1.2, fun l' hl' => h2 l' (List.mem_cons_of_mem _ hl'), h3.2⟩, h1.1,
    h2 l List.mem_cons_self, h3.1⟩

theorem entry_one (QQ : K → M2 A) (w : List (Letter K S)) (hw : Good w) :
    RRw QQ w e1 e1 = (w.reverse.map fun l => QQ l.pt 0 0).prod := by
  induction w with
  | nil => simp [RRw]
  | cons l w ih =>
    obtain ⟨hg, hs, _, hr⟩ := good_cons hw
    have hM : FreeOf2 l.intersection_update_fsHerm_neg_one (if l.plus then TTw QQ w l.pt else (TTw QQ w l.pt)ᵀ) := by
      split_ifs
      · exact freeOf_transfer_word_matrix QQ w hs _
      · exact freeOf2_transpose (freeOf_transfer_word_matrix QQ w hs _)
    have h00 : (if l.plus then TTw QQ w l.pt else (TTw QQ w l.pt)ᵀ) 0 0 = TTw QQ w l.pt 0 0 := by
      split_ifs <;> rfl
    simp only [RRw]
    rw [entry_ins l.intersection_update_fsHerm_neg_one _ _ (free_RRw QQ w hs) hM, h00, Matrix.mul_apply]
    simp only [TTw_corner QQ w l.pt hg.1 hr]
    simp [ih hg]

end Words

section Sites

variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem lift_reduction_mul (M N : M2 A) : (lift0 (M * N) : M2 (SlopeTestRemainingChoices S A)) = lift0 M * lift0 N := by
  have h : (io : A → SlopeTestRemainingChoices S A) = ⇑(Matrix.scalar (Ix S)) := rfl
  unfold lift0
  rw [h, Matrix.map_mul]

theorem io_star (x : A) : star (io x : SlopeTestRemainingChoices S A) = io (star x) := by
  ext z y
  rw [Matrix.star_apply, io_apply, io_apply]
  by_cases h : z = y
  · simp [h]
  · have h' : ¬ y = z := fun e => h e.symm
    simp [h, h']

theorem liftMatrix_conjTranspose (M : M2 A) : (lift0 M : M2 (SlopeTestRemainingChoices S A))ᴴ = lift0 Mᴴ := by
  ext1 i j
  exact io_star (M j i)

theorem liftMatrix_transpose (M : M2 A) : (lift0 M : M2 (SlopeTestRemainingChoices S A))ᵀ = lift0 Mᵀ := rfl

theorem transpose_mul_of_comm {B : Type} [Ring B] (M N : M2 B)
    (h : ∀ i j k l, Commute (M i j) (N k l)) : (M * N)ᵀ = Nᵀ * Mᵀ := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun m _ => (h j m m i).eq

theorem commute_Avr_Bvr_of_commute_siteOps (σ : Site A) (Y : K) (z : A) (hz : ∀ x ∈ hol σ, Commute z x) (i j : Fin 2) :
    Commute z (Ts σ Y i j) := by
  have hp : Commute z σ.p := hz _ (by simp [hol])
  have hc : Commute z σ.c := hz _ (by simp [hol])
  have hci : Commute z σ.ci := hz _ (by simp [hol])
  have ha : Commute z (algebraMap K A Y) := (Algebra.commutes Y z).symm
  fin_cases i <;> fin_cases j <;> simp [Ts, Tm]
  · exact ha.add_right hp
  · exact hc
  · exact hci

theorem comm_Tstar (σ : Site A) (Y : K) (z : A) (hz : ∀ x ∈ hol σ, Commute z (star x)) (i j : Fin 2) :
    Commute z (star (Ts σ Y i j)) := by
  have hp : Commute z (star σ.p) := hz _ (by simp [hol])
  have hc : Commute z (star σ.c) := hz _ (by simp [hol])
  have hci : Commute z (star σ.ci) := hz _ (by simp [hol])
  have ha : Commute z (star (algebraMap K A Y)) := by
    rw [← algebraMap_star_comm]
    exact (Algebra.commutes _ z).symm
  fin_cases i <;> fin_cases j <;> simp only [Ts, Tm] <;> simp
  · rw [← algebraMap_star_comm] at ha ⊢
    exact ha.add_right hp
  · exact hc
  · exact hci

theorem mem_ops_hol {σ : Site A} {x : A} (hx : x ∈ hol σ) : x ∈ ops σ := Or.inl hx
theorem mem_ops_star {σ : Site A} {x : A} (hx : x ∈ hol σ) : star x ∈ ops σ :=
  Or.inr (by rw [star_star]; exact hx)

theorem comm_T_Tstar (σ : Site A) (hσ : IsSite σ) (Y Y' : K) (i j k l : Fin 2) :
    Commute (Ts σ Y i j) (star (Ts σ Y' k l)) := by
  refine comm_Tstar σ Y' _ (fun x hx => ?_) k l
  refine (commute_Avr_Bvr_of_commute_siteOps σ Y _ (fun y hy => ?_) i j).symm
  exact (hσ.2 y hy x hx).symm

theorem comm_bT (σ : Site A) (w : List (Letter K S)) (z : A) (hz : ∀ x ∈ ops σ, Commute z x) :
    Commute (io z : SlopeTestRemainingChoices S A) (bT σ w) := by
  induction w with
  | nil => exact Commute.one_right _
  | cons l w ih =>
    simp only [bT, vlet]
    refine Commute.mul_right (ins_comm _ _ _ (free_io _ _) fun i j => ?_) ih
    split_ifs
    · exact io_comm_io (commute_Avr_Bvr_of_commute_siteOps σ l.pt z (fun x hx => hz x (mem_ops_hol hx)) i j)
    · exact io_comm_io (comm_Tstar σ l.pt z (fun x hx => hz _ (mem_ops_star hx)) i j)

theorem free_bT {c : S} (σ : Site A) (w : List (Letter K S)) (hc : c ∉ w.map Letter.intersection_update_fsHerm_neg_one) :
    FreeOf c (bT σ w) := by
  induction w with
  | nil => exact free_one c
  | cons l w ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hc
    simp only [bT, vlet]
    exact free_mul (ins_free hc.1 _ (freeOf2_lift c _)) (ih hc.2)

theorem scalar_commute_R_matrix_entry (a : S) (D : K) (z : A) (i j : Fin 2) :
    Commute (io z : SlopeTestRemainingChoices S A) (Rh0 a D i j) := by
  have h : (Rh0 a D : M2 (SlopeTestRemainingChoices S A)) i j =
      (D - 1)⁻¹ • (D • (1 : M2 (SlopeTestRemainingChoices S A)) i j - eU a j i) := rfl
  rw [h]
  refine Commute.smul_right (Commute.sub_right (Commute.smul_right ?_ _) (io_comm_eU a j i z).symm) _
  rw [Matrix.one_apply]
  split_ifs
  · exact Commute.one_right _
  · exact Commute.zero_right _

theorem scalar_commute_transposed_R_matrix_entry (a : S) (D : K) (z : A) (i j : Fin 2) :
    Commute (io z : SlopeTestRemainingChoices S A) (Rht0 a D i j) := by
  have h : (Rht0 a D : M2 (SlopeTestRemainingChoices S A)) i j =
      (D - 1)⁻¹ • (D • (1 : M2 (SlopeTestRemainingChoices S A)) i j - eU a i j) := rfl
  rw [h]
  refine Commute.smul_right (Commute.sub_right (Commute.smul_right ?_ _) (io_comm_eU a i j z).symm) _
  rw [Matrix.one_apply]
  split_ifs
  · exact Commute.one_right _
  · exact Commute.zero_right _

theorem commute_matrix_mul_entry {b : SlopeTestRemainingChoices S A} {M N : M2 (SlopeTestRemainingChoices S A)} (hM : ∀ i j, Commute b (M i j))
    (hN : ∀ i j, Commute b (N i j)) (i j : Fin 2) : Commute b ((M * N) i j) := by
  rw [Matrix.mul_apply]
  exact Commute.sum_right _ _ _ fun m _ => (hM i m).mul_right (hN m j)

theorem comm_TTw (QQ : K → M2 A) (w : List (Letter K S)) (z : A)
    (hz : ∀ Y i j, Commute z (QQ Y i j)) (Y : K) (i j : Fin 2) :
    Commute (io z : SlopeTestRemainingChoices S A) (TTw QQ w Y i j) := by
  induction w generalizing i j with
  | nil => exact io_comm_io (hz Y i j)
  | cons l w ih =>
    by_cases h : l.plus
    · rw [show TTw QQ (l :: w) Y = TTw QQ w Y * Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) from by simp [TTw, h]]
      exact commute_matrix_mul_entry ih (scalar_commute_R_matrix_entry _ _ z) i j
    · rw [show TTw QQ (l :: w) Y = Rht0 l.intersection_update_fsHerm_neg_one (l.pt - Y) * TTw QQ w Y from by simp [TTw, h]]
      exact commute_matrix_mul_entry (scalar_commute_transposed_R_matrix_entry _ _ z) ih i j

theorem comm_RRw (QQ : K → M2 A) (w : List (Letter K S)) (z : A)
    (hz : ∀ Y i j, Commute z (QQ Y i j)) : Commute (io z : SlopeTestRemainingChoices S A) (RRw QQ w) := by
  induction w with
  | nil => exact Commute.one_right _
  | cons l w ih =>
    simp only [RRw]
    refine ih.mul_right (ins_comm _ _ _ (free_io _ _) fun i j => ?_)
    split_ifs
    · exact comm_TTw QQ w z hz _ i j
    · exact comm_TTw QQ w z hz _ j i

theorem liftMatrix_commute_diagScalar (Q : M2 A) (b : SlopeTestRemainingChoices S A) (h : ∀ i j, Commute (io (Q i j) : SlopeTestRemainingChoices S A) b) :
    (lift0 Q : M2 (SlopeTestRemainingChoices S A)) * d0 b = d0 b * lift0 Q := by
  ext1 i j
  unfold d0 lift0
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact (h i j).eq

theorem TTw_transpose (QQ : K → M2 A) (w : List (Letter K S)) (hn : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup)
    (Y : K) : (TTw QQ w Y)ᵀ = (Xp w Y)ᵀ * lift0 (QQ Y)ᵀ * (Xm w Y)ᵀ := by
  induction w with
  | nil => simp [TTw, Xm, Xp, liftMatrix_transpose]
  | cons l w ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    by_cases h : l.plus
    · rw [show TTw QQ (l :: w) Y = TTw QQ w Y * Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) from by simp [TTw, h],
        show (Xp (l :: w) Y : M2 (SlopeTestRemainingChoices S A)) = Xp w Y * Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) from by simp [Xp, h],
        show (Xm (l :: w) Y : M2 (SlopeTestRemainingChoices S A)) = Xm w Y from by simp [Xm, h]]
      rw [transpose_mul_of_comm, transpose_mul_of_comm, ih hn.2]
      · simp only [mul_assoc]
      · intro i j k m
        have h1 : (Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) : M2 (SlopeTestRemainingChoices S A)) k m =
          (Y - l.pt - 1)⁻¹ • ((Y - l.pt) • (1 : M2 (SlopeTestRemainingChoices S A)) k m - eU l.intersection_update_fsHerm_neg_one m k) := rfl
        rw [h1]
        refine Commute.smul_right (Commute.sub_right (Commute.smul_right ?_ _)
          (freeOf_positive_word_matrix w hn.1 Y i j m k).symm) _
        rw [Matrix.one_apply]
        split_ifs
        · exact Commute.one_right _
        · exact Commute.zero_right _
      · intro i j k m
        have h1 : (Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) : M2 (SlopeTestRemainingChoices S A)) k m =
          (Y - l.pt - 1)⁻¹ • ((Y - l.pt) • (1 : M2 (SlopeTestRemainingChoices S A)) k m - eU l.intersection_update_fsHerm_neg_one m k) := rfl
        rw [h1]
        refine Commute.smul_right (Commute.sub_right (Commute.smul_right ?_ _)
          (freeOf_transfer_word_matrix QQ w hn.1 Y i j m k).symm) _
        rw [Matrix.one_apply]
        split_ifs
        · exact Commute.one_right _
        · exact Commute.zero_right _
    · rw [show TTw QQ (l :: w) Y = Rht0 l.intersection_update_fsHerm_neg_one (l.pt - Y) * TTw QQ w Y from by simp [TTw, h],
        show (Xp (l :: w) Y : M2 (SlopeTestRemainingChoices S A)) = Xp w Y from by simp [Xp, h],
        show (Xm (l :: w) Y : M2 (SlopeTestRemainingChoices S A)) = Rht0 l.intersection_update_fsHerm_neg_one (l.pt - Y) * Xm w Y from by simp [Xm, h]]
      rw [transpose_mul_of_comm, transpose_mul_of_comm, ih hn.2]
      · simp only [mul_assoc]
      · intro i j k m
        have h1 : (Rht0 l.intersection_update_fsHerm_neg_one (l.pt - Y) : M2 (SlopeTestRemainingChoices S A)) i j =
          (l.pt - Y - 1)⁻¹ • ((l.pt - Y) • (1 : M2 (SlopeTestRemainingChoices S A)) i j - eU l.intersection_update_fsHerm_neg_one i j) := rfl
        rw [h1]
        refine Commute.smul_left (Commute.sub_left (Commute.smul_left ?_ _)
          (freeOf_negative_word_matrix w hn.1 Y k m i j)) _
        rw [Matrix.one_apply]
        split_ifs
        · exact Commute.one_left _
        · exact Commute.zero_left _
      · intro i j k m
        have h1 : (Rht0 l.intersection_update_fsHerm_neg_one (l.pt - Y) : M2 (SlopeTestRemainingChoices S A)) i j =
          (l.pt - Y - 1)⁻¹ • ((l.pt - Y) • (1 : M2 (SlopeTestRemainingChoices S A)) i j - eU l.intersection_update_fsHerm_neg_one i j) := rfl
        rw [h1]
        refine Commute.smul_left (Commute.sub_left (Commute.smul_left ?_ _)
          (freeOf_transfer_word_matrix QQ w hn.1 Y k m i j)) _
        rw [Matrix.one_apply]
        split_ifs
        · exact Commute.one_left _
        · exact Commute.zero_left _

end Sites

section Step

variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem QQ_transpose (σ : Site A) (hσ : IsSite σ) (Q : M2 A) (Y : K)
    (hQ : ∀ i j, ∀ x ∈ ops σ, Commute (Q i j) x) :
    ((Ts σ Y)ᴴ * Q * Ts σ Y)ᵀ = (Ts σ Y)ᵀ * Qᵀ * (Ts σ Y).map star := by
  have hQT : ∀ i j k l, Commute (Q i j) (Ts σ Y k l) := fun i j k l =>
    commute_Avr_Bvr_of_commute_siteOps σ Y _ (fun x hx => hQ i j x (mem_ops_hol hx)) k l
  have hQS : ∀ i j k l, Commute (Q i j) (star (Ts σ Y k l)) := fun i j k l =>
    comm_Tstar σ Y _ (fun x hx => hQ i j _ (mem_ops_star hx)) k l
  rw [transpose_mul_of_comm, transpose_mul_of_comm]
  · rw [mul_assoc]
    rfl
  · intro i j k l
    exact (hQS k l j i).symm
  · intro i j k l
    rw [Matrix.mul_apply]
    refine Commute.sum_left _ _ _ fun m _ => Commute.mul_left ?_ (hQT m j k l)
    exact (comm_T_Tstar σ hσ Y Y k l m i).symm

theorem site_step_of
    (hE1 : ExchangePlusFactor) (hE2 : ExchangeMinusFactorStar) (hE3 : ExchangeMinusFactorTranspose) (hE4 : ExchangePlusFactorTranspose)
    (σ : Site A) (QQ QQ' : K → M2 A) (w : List (Letter K S))
    (hσ : IsSite σ) (hQ : QQCommutes QQ σ)
    (hrec : ∀ Y, star Y = Y → QQ' Y = (Ts σ Y)ᴴ * QQ Y * Ts σ Y) (hw : Good w) :
    star (bT σ w) * RRw QQ w * bT σ w = RRw QQ' w := by
  induction w with
  | nil => simp [bT, RRw]
  | cons l w ih =>
    obtain ⟨hg, hs, hre, -⟩ := good_cons hw
    have ih := ih hg
    have e1 := hE1 K A S σ w l.pt hσ hg
    have e2 := hE2 K A S σ w l.pt hσ hg hre
    have e3 := hE3 K A S σ w l.pt hσ hg hre
    have e4 := hE4 K A S σ w l.pt hσ hg
    have hfb : FreeOf l.intersection_update_fsHerm_neg_one (bT σ w) := free_bT σ w hs
    have hfR : FreeOf l.intersection_update_fsHerm_neg_one (RRw QQ w) := free_RRw QQ w hs
    have hQB : (lift0 (QQ l.pt) : M2 (SlopeTestRemainingChoices S A)) * d0 (bT σ w) = d0 (bT σ w) * lift0 (QQ l.pt) :=
      liftMatrix_commute_diagScalar _ _ fun i j => comm_bT σ w _ (hQ l.pt i j)
    have hQBt : (lift0 (QQ l.pt)ᵀ : M2 (SlopeTestRemainingChoices S A)) * d0 (bT σ w) = d0 (bT σ w) * lift0 (QQ l.pt)ᵀ :=
      liftMatrix_commute_diagScalar _ _ fun i j => comm_bT σ w _ (hQ l.pt j i)
    by_cases h : l.plus
    · have hb : bT σ (l :: w) = ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)) * bT σ w := by simp [bT, vlet, h]
      have hR : RRw QQ (l :: w) = RRw QQ w * ins l.intersection_update_fsHerm_neg_one (TTw QQ w l.pt) := by simp [RRw, h]
      have hR' : RRw QQ' (l :: w) = RRw QQ' w * ins l.intersection_update_fsHerm_neg_one (TTw QQ' w l.pt) := by simp [RRw, h]
      have hst : star (ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)) : SlopeTestRemainingChoices S A) = ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)ᴴ) := by
        rw [ins_star _ _ (freeOf2_lift _ _), liftMatrix_conjTranspose]
      have hcomm : Commute (RRw QQ w) (ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)ᴴ)) := by
        refine ins_comm _ _ _ hfR fun i j => ?_
        refine (comm_RRw QQ w _ fun Y i' j' => ?_).symm
        exact (comm_Tstar σ l.pt _ (fun x hx => hQ Y i' j' _ (mem_ops_star hx)) j i).symm
      have hM : (lift0 (Ts σ l.pt)ᴴ : M2 (SlopeTestRemainingChoices S A)) * TTw QQ w l.pt * lift0 (Ts σ l.pt) * d0 (bT σ w) =
          d0 (bT σ w) * TTw QQ' w l.pt := by
        rw [TTw_factor, TTw_factor, hrec l.pt hre, lift_reduction_mul, lift_reduction_mul]
        calc (lift0 (Ts σ l.pt)ᴴ : M2 (SlopeTestRemainingChoices S A)) * (Xm w l.pt * lift0 (QQ l.pt) * Xp w l.pt) *
              lift0 (Ts σ l.pt) * d0 (bT σ w)
            = lift0 (Ts σ l.pt)ᴴ * Xm w l.pt * lift0 (QQ l.pt) *
                (Xp w l.pt * lift0 (Ts σ l.pt) * d0 (bT σ w)) := by simp only [mul_assoc]
          _ = lift0 (Ts σ l.pt)ᴴ * Xm w l.pt * (lift0 (QQ l.pt) * d0 (bT σ w)) *
                lift0 (Ts σ l.pt) * Xp w l.pt := by rw [e1]; simp only [mul_assoc]
          _ = (lift0 (Ts σ l.pt)ᴴ * Xm w l.pt * d0 (bT σ w)) * lift0 (QQ l.pt) *
                lift0 (Ts σ l.pt) * Xp w l.pt := by rw [hQB]; simp only [mul_assoc]
          _ = d0 (bT σ w) * (Xm w l.pt * (lift0 (Ts σ l.pt)ᴴ * lift0 (QQ l.pt) * lift0 (Ts σ l.pt)) *
                Xp w l.pt) := by rw [e2]; simp only [mul_assoc]
      have hI : (ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)ᴴ) : SlopeTestRemainingChoices S A) * ins l.intersection_update_fsHerm_neg_one (TTw QQ w l.pt) *
          ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)) * bT σ w = bT σ w * ins l.intersection_update_fsHerm_neg_one (TTw QQ' w l.pt) := by
        rw [← ins_mul _ _ _ (freeOf2_lift _ _),
          ← ins_mul _ _ _ (freeOf2_mul (freeOf2_lift _ _) (freeOf_transfer_word_matrix QQ w hs _)),
          ← insert_mul_diagScalar, hM, insert_diagScalar_mul_of_free _ _ _ hfb]
      rw [hb, hR, hR', star_mul, hst, ← ih]
      calc star (bT σ w) * ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)ᴴ) * (RRw QQ w * ins l.intersection_update_fsHerm_neg_one (TTw QQ w l.pt)) *
            (ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)) * bT σ w)
          = star (bT σ w) * (ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)ᴴ) * RRw QQ w) * ins l.intersection_update_fsHerm_neg_one (TTw QQ w l.pt) *
            ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)) * bT σ w := by simp only [mul_assoc]
        _ = star (bT σ w) * RRw QQ w * (ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)ᴴ) * ins l.intersection_update_fsHerm_neg_one (TTw QQ w l.pt) *
            ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)) * bT σ w) := by rw [← hcomm.eq]; simp only [mul_assoc]
        _ = _ := by rw [hI]; simp only [mul_assoc]
    · have hb : bT σ (l :: w) = ins l.intersection_update_fsHerm_neg_one (lift0 ((Ts σ l.pt).map star)) * bT σ w := by
        simp [bT, vlet, h]
      have hR : RRw QQ (l :: w) = RRw QQ w * ins l.intersection_update_fsHerm_neg_one (TTw QQ w l.pt)ᵀ := by simp [RRw, h]
      have hR' : RRw QQ' (l :: w) = RRw QQ' w * ins l.intersection_update_fsHerm_neg_one (TTw QQ' w l.pt)ᵀ := by simp [RRw, h]
      have hst : star (ins l.intersection_update_fsHerm_neg_one (lift0 ((Ts σ l.pt).map star)) : SlopeTestRemainingChoices S A) =
          ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)ᵀ) := by
        rw [ins_star _ _ (freeOf2_lift _ _), liftMatrix_conjTranspose]
        congr 2
        ext i j
        simp
      have hcomm : Commute (RRw QQ w) (ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)ᵀ)) := by
        refine ins_comm _ _ _ hfR fun i j => ?_
        refine (comm_RRw QQ w _ fun Y i' j' => ?_).symm
        exact (commute_Avr_Bvr_of_commute_siteOps σ l.pt _ (fun x hx => hQ Y i' j' _ (mem_ops_hol hx)) j i).symm
      have hM : (lift0 (Ts σ l.pt)ᵀ : M2 (SlopeTestRemainingChoices S A)) * (TTw QQ w l.pt)ᵀ *
          lift0 ((Ts σ l.pt).map star) * d0 (bT σ w) = d0 (bT σ w) * (TTw QQ' w l.pt)ᵀ := by
        rw [TTw_transpose _ _ hg.1, TTw_transpose _ _ hg.1, hrec l.pt hre,
          QQ_transpose σ hσ _ _ (hQ l.pt), lift_reduction_mul, lift_reduction_mul]
        calc (lift0 (Ts σ l.pt)ᵀ : M2 (SlopeTestRemainingChoices S A)) *
              ((Xp w l.pt)ᵀ * lift0 (QQ l.pt)ᵀ * (Xm w l.pt)ᵀ) *
              lift0 ((Ts σ l.pt).map star) * d0 (bT σ w)
            = lift0 (Ts σ l.pt)ᵀ * (Xp w l.pt)ᵀ * lift0 (QQ l.pt)ᵀ *
                ((Xm w l.pt)ᵀ * lift0 ((Ts σ l.pt).map star) * d0 (bT σ w)) := by
              simp only [mul_assoc]
          _ = lift0 (Ts σ l.pt)ᵀ * (Xp w l.pt)ᵀ * (lift0 (QQ l.pt)ᵀ * d0 (bT σ w)) *
                lift0 ((Ts σ l.pt).map star) * (Xm w l.pt)ᵀ := by rw [e3]; simp only [mul_assoc]
          _ = (lift0 (Ts σ l.pt)ᵀ * (Xp w l.pt)ᵀ * d0 (bT σ w)) * lift0 (QQ l.pt)ᵀ *
                lift0 ((Ts σ l.pt).map star) * (Xm w l.pt)ᵀ := by rw [hQBt]; simp only [mul_assoc]
          _ = d0 (bT σ w) * ((Xp w l.pt)ᵀ * (lift0 (Ts σ l.pt)ᵀ * lift0 (QQ l.pt)ᵀ *
                lift0 ((Ts σ l.pt).map star)) * (Xm w l.pt)ᵀ) := by rw [e4]; simp only [mul_assoc]
      have hI : (ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)ᵀ) : SlopeTestRemainingChoices S A) * ins l.intersection_update_fsHerm_neg_one (TTw QQ w l.pt)ᵀ *
          ins l.intersection_update_fsHerm_neg_one (lift0 ((Ts σ l.pt).map star)) * bT σ w =
          bT σ w * ins l.intersection_update_fsHerm_neg_one (TTw QQ' w l.pt)ᵀ := by
        rw [← ins_mul _ _ _ (freeOf2_lift _ _),
          ← ins_mul _ _ _ (freeOf2_mul (freeOf2_lift _ _) (freeOf2_transpose (freeOf_transfer_word_matrix QQ w hs _))),
          ← insert_mul_diagScalar, hM, insert_diagScalar_mul_of_free _ _ _ hfb]
      rw [hb, hR, hR', star_mul, hst, ← ih]
      calc star (bT σ w) * ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)ᵀ) * (RRw QQ w * ins l.intersection_update_fsHerm_neg_one (TTw QQ w l.pt)ᵀ) *
            (ins l.intersection_update_fsHerm_neg_one (lift0 ((Ts σ l.pt).map star)) * bT σ w)
          = star (bT σ w) * (ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)ᵀ) * RRw QQ w) * ins l.intersection_update_fsHerm_neg_one (TTw QQ w l.pt)ᵀ *
            ins l.intersection_update_fsHerm_neg_one (lift0 ((Ts σ l.pt).map star)) * bT σ w := by simp only [mul_assoc]
        _ = star (bT σ w) * RRw QQ w * (ins l.intersection_update_fsHerm_neg_one (lift0 (Ts σ l.pt)ᵀ) * ins l.intersection_update_fsHerm_neg_one (TTw QQ w l.pt)ᵀ *
            ins l.intersection_update_fsHerm_neg_one (lift0 ((Ts σ l.pt).map star)) * bT σ w) := by
              rw [← hcomm.eq]; simp only [mul_assoc]
        _ = _ := by rw [hI]; simp only [mul_assoc]

end Step

end Formalism.FourierDecayAlt.P.Wd7

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.Wd

theorem positive_word_fixed : Formalism.FourierDecayAlt.Wd.XpFix := by
  intro K A S _ _ _ _ _ _ _ _ w Y _ hr k z
  exact Wd7.Xp_fix w Y hr k z

theorem negative_word_fixed : Formalism.FourierDecayAlt.Wd.XmFix := by
  intro K A S _ _ _ _ _ _ _ _ w Y hn hr k z
  exact Wd7.Xm_fix w Y hn hr k z

theorem word_matrix_entry_one : Formalism.FourierDecayAlt.Wd.EntryOne := by
  intro K A S _ _ _ _ _ _ _ _ QQ w hw
  exact Wd7.entry_one QQ w hw

theorem wd_siteStep_of (hE1 : Formalism.FourierDecayAlt.Wd.ExchangePlusFactor) (hE2 : Formalism.FourierDecayAlt.Wd.ExchangeMinusFactorStar)
    (hE3 : Formalism.FourierDecayAlt.Wd.ExchangeMinusFactorTranspose) (hE4 : Formalism.FourierDecayAlt.Wd.ExchangePlusFactorTranspose) : Formalism.FourierDecayAlt.Wd.SiteStep := by
  intro K A S _ _ _ _ _ _ _ _ σ QQ QQ' w hσ hQ hrec hw
  exact Wd7.site_step_of hE1 hE2 hE3 hE4 σ QQ QQ' w hσ hQ hrec hw

theorem site_exchange_relation : Formalism.FourierDecayAlt.Wd.SiteStep :=
  wd_siteStep_of exchange_plus_factor exchange_second_case exchange_third_case exchange_fourth_case

end Formalism.FourierDecayAlt.P
