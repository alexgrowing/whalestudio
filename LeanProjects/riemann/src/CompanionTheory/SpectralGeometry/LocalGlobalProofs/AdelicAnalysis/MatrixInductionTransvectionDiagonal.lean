import Mathlib

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic.StableRangeOne

def elem (R : Type) [CommRing R] (ι : Type) [Fintype ι] [DecidableEq ι] :
    Submonoid (Matrix ι ι R) :=
  Submonoid.closure ({T | ∃ i j c, i ≠ j ∧ T = Matrix.transvection i j c} ∪
    {T | ∃ D : ι → R, (∀ i, IsUnit (D i)) ∧ T = Matrix.diagonal D})

def rowOp {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (k : ι) (c : ι → R) : Matrix ι ι R :=
  1 + Matrix.of fun i j => if i = k then c j else 0

def colOp {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (k : ι) (c : ι → R) : Matrix ι ι R :=
  1 + Matrix.of fun i j => if j = k then c i else 0

def Fixed {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (A : Matrix ι ι R) : Prop :=
  ∀ i j, (i ∉ s ∨ j ∉ s) → A i j = (1 : Matrix ι ι R) i j

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

lemma transvection_mem {i j : ι} (h : i ≠ j) (c : R) :
    Matrix.transvection i j c ∈ elem R ι :=
  Submonoid.subset_closure (Or.inl ⟨i, j, c, h, rfl⟩)

lemma diagonal_mem {D : ι → R} (h : ∀ i, IsUnit (D i)) : Matrix.diagonal D ∈ elem R ι :=
  Submonoid.subset_closure (Or.inr ⟨D, h, rfl⟩)

lemma exists_left_inv {A : Matrix ι ι R} (hA : A ∈ elem R ι) :
    ∃ B ∈ elem R ι, B * A = 1 := by
  induction hA using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with ⟨i, j, c, h, rfl⟩ | ⟨D, hD, rfl⟩
    · refine ⟨Matrix.transvection i j (-c), transvection_mem h _, ?_⟩
      rw [Matrix.transvection_mul_transvection_same _ _ h]
      simp
    · refine ⟨Matrix.diagonal (fun i => (((hD i).unit⁻¹ : Rˣ) : R)),
        diagonal_mem (fun i => Units.isUnit _), ?_⟩
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact (hD i).val_inv_mul
  | one => exact ⟨1, one_mem _, one_mul _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, ha'⟩ := hx
    obtain ⟨b, hb, hb'⟩ := hy
    exact ⟨b * a, mul_mem hb ha, by rw [mul_assoc, ← mul_assoc a, ha', one_mul, hb']⟩

lemma mem_of_mul_left {T A : Matrix ι ι R} (hT : T ∈ elem R ι) (h : T * A ∈ elem R ι) :
    A ∈ elem R ι := by
  obtain ⟨B, hB, hBT⟩ := exists_left_inv hT
  have : A = B * (T * A) := by rw [← mul_assoc, hBT, one_mul]
  rw [this]
  exact mul_mem hB h

lemma mem_of_mul_right {T A : Matrix ι ι R} (hT : T ∈ elem R ι) (h : A * T ∈ elem R ι) :
    A ∈ elem R ι := by
  obtain ⟨B, hB, hBT⟩ := exists_left_inv hT
  have hTB : T * B = 1 := mul_eq_one_comm.mp hBT
  have : A = (A * T) * B := by rw [mul_assoc, hTB, mul_one]
  rw [this]
  exact mul_mem h hB

lemma isUnit_det_of_mem {A : Matrix ι ι R} (hA : A ∈ elem R ι) : IsUnit A.det := by
  obtain ⟨B, _, hBA⟩ := exists_left_inv hA
  have : B.det * A.det = 1 := by rw [← Matrix.det_mul, hBA, Matrix.det_one]
  exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact this)

lemma rowOp_mem (k : ι) (c : ι → R) (hc : c k = 0) : rowOp k c ∈ elem R ι := by
  have key : ∀ t : Finset ι, k ∉ t → rowOp k (fun j => if j ∈ t then c j else 0) ∈ elem R ι := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      have : rowOp k (fun j => if j ∈ (∅ : Finset ι) then c j else 0) = (1 : Matrix ι ι R) := by
        ext a b
        simp [rowOp]
      rw [this]
      exact one_mem _
    | insert i t hi ih =>
      intro hk
      have hki : k ≠ i := fun h => hk (h ▸ Finset.mem_insert_self _ _)
      have hkt : k ∉ t := fun h => hk (Finset.mem_insert_of_mem h)
      have : rowOp k (fun j => if j ∈ insert i t then c j else 0) =
          rowOp k (fun j => if j ∈ t then c j else 0) * Matrix.transvection k i (c i) := by
        ext a b
        by_cases hb : b = i
        · subst hb
          rw [Matrix.mul_transvection_apply_same]
          by_cases ha : a = k
          · subst ha
            simp [rowOp, Matrix.one_apply, hi, hki, hkt]
          · simp [rowOp, Matrix.one_apply, ha]
        · rw [Matrix.mul_transvection_apply_of_ne _ _ _ _ hb]
          simp [rowOp, Finset.mem_insert, hb]
      rw [this]
      exact mul_mem (ih hkt) (transvection_mem hki _)
  have := key (Finset.univ.erase k) (by simp)
  convert this using 2
  funext j
  by_cases h : j = k
  · subst h; simp [hc]
  · simp [h]

lemma colOp_mem (k : ι) (c : ι → R) (hc : c k = 0) : colOp k c ∈ elem R ι := by
  have key : ∀ t : Finset ι, k ∉ t → colOp k (fun j => if j ∈ t then c j else 0) ∈ elem R ι := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      have : colOp k (fun j => if j ∈ (∅ : Finset ι) then c j else 0) = (1 : Matrix ι ι R) := by
        ext a b
        simp [colOp]
      rw [this]
      exact one_mem _
    | insert i t hi ih =>
      intro hk
      have hki : k ≠ i := fun h => hk (h ▸ Finset.mem_insert_self _ _)
      have hkt : k ∉ t := fun h => hk (Finset.mem_insert_of_mem h)
      have : colOp k (fun j => if j ∈ insert i t then c j else 0) =
          Matrix.transvection i k (c i) * colOp k (fun j => if j ∈ t then c j else 0) := by
        ext a b
        by_cases ha : a = i
        · subst ha
          rw [Matrix.transvection_mul_apply_same]
          by_cases hb : b = k
          · subst hb
            simp [colOp, Matrix.one_apply, hi, hki.symm, hkt]
          · simp [colOp, Matrix.one_apply, hb, Ne.symm hb]
        · rw [Matrix.transvection_mul_apply_of_ne _ _ _ _ ha]
          simp [colOp, Finset.mem_insert, ha]
      rw [this]
      exact mul_mem (transvection_mem hki.symm _) (ih hkt)
  have := key (Finset.univ.erase k) (by simp)
  convert this using 2
  funext j
  by_cases h : j = k
  · subst h; simp [hc]
  · simp [h]

lemma rowOp_mul_apply (k : ι) (c : ι → R) (A : Matrix ι ι R) (i j : ι) :
    (rowOp k c * A) i j = A i j + if i = k then ∑ l, c l * A l j else 0 := by
  rw [rowOp, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  by_cases h : i = k <;> simp [h]

lemma colOp_mul_apply (k : ι) (c : ι → R) (A : Matrix ι ι R) (i j : ι) :
    (colOp k c * A) i j = A i j + c i * A k j := by
  rw [colOp, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  simp

lemma mul_rowOp_apply (k : ι) (c : ι → R) (A : Matrix ι ι R) (i j : ι) :
    (A * rowOp k c) i j = A i j + A i k * c j := by
  rw [rowOp, mul_add, mul_one, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  simp

lemma mem_of_unit_pivot {s : Finset ι} {k : ι}
    (ih : ∀ A : Matrix ι ι R, IsUnit A.det → Fixed s A → A ∈ elem R ι)
    {A : Matrix ι ι R} (hA : IsUnit A.det) (hF : Fixed (insert k s) A)
    (hk : k ∉ s) (hu : IsUnit (A k k)) : A ∈ elem R ι := by
  obtain ⟨ui, hui⟩ := hu.exists_right_inv
  set v : ι → R := fun i => if i = k then 0 else -(A i k * ui) with hv
  set x : ι → R := fun j => if j = k then 0 else -(ui * A k j) with hx
  set D : ι → R := Function.update (fun _ => 1) k ui with hD
  have hDu : ∀ i, IsUnit (D i) := by
    intro i
    by_cases h : i = k
    · subst h
      simp only [hD, Function.update_self]
      exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hui)
    · simp [hD, Function.update_of_ne h]
  have hCm := colOp_mem k v (by simp [hv])
  have hRm := rowOp_mem k x (by simp [hx])
  have hDm := diagonal_mem hDu
  set A4 : Matrix ι ι R := Matrix.diagonal D * ((colOp k v * A) * rowOp k x) with hA4
  have entry : ∀ i j, A4 i j = D i * ((A i j + v i * A k j) +
      (A i k + v i * A k k) * x j) := by
    intro i j
    rw [hA4, Matrix.diagonal_mul, mul_rowOp_apply, colOp_mul_apply, colOp_mul_apply]
  have hF4 : Fixed s A4 := by
    intro i j hij
    rw [entry]
    by_cases hi : i = k
    · subst hi
      by_cases hj : j = i
      · subst hj
        simp [hv, hx, hD, Matrix.one_apply]
        rw [mul_comm]; exact hui
      · have : A i i * ui = 1 := hui
        simp only [hv, hx, if_true, hj, if_false, hD, Function.update_self,
          Matrix.one_apply, Ne.symm hj]
        linear_combination (-(ui * A i j)) * this
    · by_cases hj : j = k
      · subst hj
        simp [hv, hx, hi, hD, Function.update_of_ne hi, Matrix.one_apply]
        have : A j j * ui = 1 := hui
        linear_combination (-A i j) * this
      · have hDi : D i = 1 := by simp [hD, Function.update_of_ne hi]
        have hvx : (A i k + v i * A k k) = 0 := by
          have : A k k * ui = 1 := hui
          simp only [hv, hi, if_false]
          linear_combination (-A i k) * this
        rw [hDi, hvx, zero_mul, add_zero, one_mul]
        rcases hij with h | h
        · have hi' : i ∉ insert k s := by simp [hi, h]
          have h0 : A i k = 0 := by
            rw [hF i k (Or.inl hi'), Matrix.one_apply_ne hi]
          rw [hF i j (Or.inl hi')]
          simp [hv, hi, h0]
        · have hj' : j ∉ insert k s := by simp [hj, h]
          have h0 : A k j = 0 := by
            rw [hF k j (Or.inr hj'), Matrix.one_apply_ne (Ne.symm hj)]
          rw [hF i j (Or.inr hj'), h0, mul_zero, add_zero]
  have hdet : IsUnit A4.det := by
    rw [hA4, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
    exact (isUnit_det_of_mem hDm).mul
      (((isUnit_det_of_mem hCm).mul hA).mul (isUnit_det_of_mem hRm))
  have h4 := ih A4 hdet hF4
  exact mem_of_mul_left hCm (mem_of_mul_right hRm (mem_of_mul_left hDm h4))

lemma exists_unit_pivot (hR : ∀ a b : R, IsCoprime a b → ∃ t, IsUnit (a + t * b))
    {s : Finset ι} {k : ι} {A : Matrix ι ι R} (hA : IsUnit A.det)
    (hF : Fixed (insert k s) A) (hk : k ∉ s) :
    ∃ w : ι → R, w k = 0 ∧ Fixed (insert k s) (rowOp k w * A) ∧
      IsUnit ((rowOp k w * A) k k) := by
  set B := A⁻¹ with hB
  have hBA : B * A = 1 := Matrix.nonsing_inv_mul A hA
  have hsum : ∑ l, B k l * A l k = 1 := by
    have := congrFun (congrFun hBA k) k
    simpa [Matrix.mul_apply] using this
  have hzero : ∀ l, l ∉ insert k s → A l k = 0 := by
    intro l hl
    have hlk : l ≠ k := fun h => hl (h ▸ Finset.mem_insert_self _ _)
    rw [hF l k (Or.inl hl), Matrix.one_apply_ne hlk]
  have hsplit : ∑ l, B k l * A l k = B k k * A k k + ∑ l ∈ s, B k l * A l k := by
    rw [← Finset.sum_insert (f := fun l => B k l * A l k) hk]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro l _ hl
    rw [hzero l hl, mul_zero]
  set b := ∑ l ∈ s, B k l * A l k with hb
  have hcop : IsCoprime (A k k) b := ⟨B k k, 1, by rw [one_mul, ← hsplit, hsum]⟩
  obtain ⟨t, ht⟩ := hR _ _ hcop
  set w : ι → R := fun l => if l ∈ s then t * B k l else 0 with hw
  have hwsum : ∀ j, ∑ l, w l * A l j = t * ∑ l ∈ s, B k l * A l j := by
    intro j
    rw [Finset.mul_sum, ← Finset.sum_subset (Finset.subset_univ s)]
    · apply Finset.sum_congr rfl
      intro l hl
      simp [hw, hl, mul_assoc]
    · intro l _ hl
      simp [hw, hl]
  refine ⟨w, by simp [hw, hk], ?_, ?_⟩
  · intro i j hij
    rw [rowOp_mul_apply]
    by_cases hi : i = k
    · subst hi
      have hj : j ∉ insert i s := by
        rcases hij with h | h
        · exact absurd (Finset.mem_insert_self _ _) h
        · exact h
      have hji : i ≠ j := fun h => hj (h ▸ Finset.mem_insert_self _ _)
      rw [if_pos rfl, hwsum, hF i j (Or.inr hj), Finset.sum_eq_zero, mul_zero, add_zero]
      intro l hl
      have hlj : l ≠ j := fun h => hj (h ▸ Finset.mem_insert_of_mem hl)
      rw [hF l j (Or.inr hj), Matrix.one_apply_ne hlj, mul_zero]
    · rw [if_neg hi, add_zero]
      exact hF i j hij
  · rw [rowOp_mul_apply, if_pos rfl, hwsum]
    exact ht

lemma mem_of_fixed (hR : ∀ a b : R, IsCoprime a b → ∃ t, IsUnit (a + t * b))
    (s : Finset ι) : ∀ A : Matrix ι ι R, IsUnit A.det → Fixed s A → A ∈ elem R ι := by
  induction s using Finset.induction_on with
  | empty =>
    intro A _ hF
    have : A = 1 := by
      ext i j
      exact hF i j (Or.inl (by simp))
    rw [this]
    exact one_mem _
  | insert k s hk ih =>
    intro A hA hF
    obtain ⟨w, hw0, hwF, hwu⟩ := exists_unit_pivot hR hA hF hk
    have hm := rowOp_mem k w hw0
    have hdet : IsUnit (rowOp k w * A).det := by
      rw [Matrix.det_mul]
      exact (isUnit_det_of_mem hm).mul hA
    exact mem_of_mul_left hm (mem_of_unit_pivot ih hdet hwF hk hwu)

theorem matrix_induction :
    ∀ (R : Type) [CommRing R], (∀ a b : R, IsCoprime a b → ∃ t, IsUnit (a + t * b)) →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (p : Matrix ι ι R → Prop),
        (∀ (i j : ι) (c : R), i ≠ j → p (Matrix.transvection i j c)) →
        (∀ D : ι → R, (∀ i, IsUnit (D i)) → p (Matrix.diagonal D)) →
        (∀ A B, IsUnit A.det → IsUnit B.det → p A → p B → p (A * B)) →
        ∀ A : Matrix ι ι R, IsUnit A.det → p A := by
  intro R _ hR ι _ _ p ht hd hm A hA
  have hmem : A ∈ elem R ι :=
    mem_of_fixed hR Finset.univ A hA (fun i j h => by simp at h)
  have key : ∀ B ∈ elem R ι, p B := by
    intro B hB
    induction hB using Submonoid.closure_induction with
    | mem x hx =>
      rcases hx with ⟨i, j, c, h, rfl⟩ | ⟨D, hD, rfl⟩
      · exact ht i j c h
      · exact hd D hD
    | one =>
      have := hd (fun _ => 1) (fun _ => isUnit_one)
      simpa using this
    | mul x y hx hy px py =>
      exact hm x y (isUnit_det_of_mem hx) (isUnit_det_of_mem hy) px py
  exact key A hmem

end GlobalTheory.CompanionTheory.Adelic.StableRangeOne
