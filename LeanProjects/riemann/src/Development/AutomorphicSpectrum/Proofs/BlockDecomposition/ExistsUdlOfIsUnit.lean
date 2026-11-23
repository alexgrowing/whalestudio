import Mathlib

namespace GlobalTheory.CompanionTheory.IwahoriUDL

open Matrix

variable {R : Type*} [CommRing R]

def ex (n : ℕ) : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv

theorem ex_inl {n : ℕ} (i : Fin n) : ex n (Sum.inl i) = i.castSucc := rfl

theorem ex_inr {n : ℕ} (k : Fin 1) : ex n (Sum.inr k) = Fin.last n := by
  have hk : k = 0 := Subsingleton.elim _ _
  subst hk
  ext
  simp [ex]

theorem one_ex {n : ℕ} (i j : Fin n ⊕ Fin 1) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (ex n i) (ex n j) =
      fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 (1 : Matrix (Fin 1) (Fin 1) R) i j := by
  rw [fromBlocks_one]
  simp [Matrix.one_apply]

def IsUp (I : Ideal R) {n : ℕ} (u : Matrix (Fin n) (Fin n) R) : Prop :=
  (∀ i j, u i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I) ∧ (∀ i j, j < i → u i j = 0) ∧
    ∀ i, u i i = 1

def IsLo (I : Ideal R) {n : ℕ} (l : Matrix (Fin n) (Fin n) R) : Prop :=
  (∀ i j, l i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I) ∧ (∀ i j, i < j → l i j = 0) ∧
    ∀ i, l i i = 1

def IsDi (I : Ideal R) {n : ℕ} (d : Matrix (Fin n) (Fin n) R) : Prop :=
  (∀ i j, d i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I) ∧ ∀ i j, i ≠ j → d i j = 0

theorem up_step {I : Ideal R} {n : ℕ} {u : Matrix (Fin n) (Fin n) R} (hu : IsUp I u)
    {x : Matrix (Fin n) (Fin 1) R} (hx : ∀ i k, x i k ∈ I) :
    IsUp I ((fromBlocks u x 0 1).submatrix (ex n).symm (ex n).symm) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    obtain ⟨j, rfl⟩ := (ex n).surjective j
    rw [one_ex, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · simpa using hu.1 i j
    · simpa using hx i j
    · simp
    · simp
  · intro i j hij
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    obtain ⟨j, rfl⟩ := (ex n).surjective j
    rw [submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · simp only [ex_inl, Fin.castSucc_lt_castSucc_iff] at hij
      simpa using hu.2.1 i j hij
    · simp only [ex_inl, ex_inr] at hij
      exact absurd hij (not_lt.mpr (Fin.le_last _))
    · simp
    · simp only [ex_inr, lt_self_iff_false] at hij
  · intro i
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    rw [submatrix_apply, Equiv.symm_apply_apply]
    rcases i with i | i
    · simpa using hu.2.2 i
    · simp

theorem lo_step {I : Ideal R} {n : ℕ} {l : Matrix (Fin n) (Fin n) R} (hl : IsLo I l)
    {y : Matrix (Fin 1) (Fin n) R} (hy : ∀ k j, y k j ∈ I) :
    IsLo I ((fromBlocks l 0 y 1).submatrix (ex n).symm (ex n).symm) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    obtain ⟨j, rfl⟩ := (ex n).surjective j
    rw [one_ex, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · simpa using hl.1 i j
    · simp
    · simpa using hy i j
    · simp
  · intro i j hij
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    obtain ⟨j, rfl⟩ := (ex n).surjective j
    rw [submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · simp only [ex_inl, Fin.castSucc_lt_castSucc_iff] at hij
      simpa using hl.2.1 i j hij
    · simp
    · simp only [ex_inl, ex_inr] at hij
      exact absurd hij (not_lt.mpr (Fin.le_last _))
    · simp only [ex_inr, lt_self_iff_false] at hij
  · intro i
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    rw [submatrix_apply, Equiv.symm_apply_apply]
    rcases i with i | i
    · simpa using hl.2.2 i
    · simp

theorem di_step {I : Ideal R} {n : ℕ} {d : Matrix (Fin n) (Fin n) R} (hd : IsDi I d)
    {a : Matrix (Fin 1) (Fin 1) R} (ha : ∀ k k', a k k' - (1 : Matrix (Fin 1) (Fin 1) R) k k' ∈ I) :
    IsDi I ((fromBlocks d 0 0 a).submatrix (ex n).symm (ex n).symm) := by
  refine ⟨?_, ?_⟩
  · intro i j
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    obtain ⟨j, rfl⟩ := (ex n).surjective j
    rw [one_ex, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · simpa using hd.1 i j
    · simp
    · simp
    · simpa using ha i j
  · intro i j hij
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    obtain ⟨j, rfl⟩ := (ex n).surjective j
    rw [submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · have : i ≠ j := fun h => hij (by rw [h])
      simpa using hd.2 i j this
    · simp
    · simp
    · exact absurd (by rw [Subsingleton.elim i j]) hij

theorem fromBlocks_udl {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (c : Matrix (Fin n) (Fin 1) R)
    (r : Matrix (Fin 1) (Fin n) R) (a b : Matrix (Fin 1) (Fin 1) R) (hab : a * b = 1)
    (hba : b * a = 1) (u d l : Matrix (Fin n) (Fin n) R) (h : A - c * b * r = u * d * l) :
    fromBlocks A c r a =
      fromBlocks u (c * b) 0 1 * fromBlocks d 0 0 a * fromBlocks l 0 (b * r) 1 := by
  have h' : A = u * d * l + c * b * r := by rw [← h]; abel
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.one_mul]
  rw [Matrix.mul_assoc c b a, hba, Matrix.mul_one, ← Matrix.mul_assoc a b r, hab, Matrix.one_mul]
  rw [h', Matrix.mul_assoc c b r]

theorem exists_udl_of_isUnit (I : Ideal R) (hI : ∀ x ∈ I, IsUnit (1 + x)) (n : ℕ) :
    ∀ g : Matrix (Fin n) (Fin n) R,
      (∀ i j, g i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I) →
        ∃ u d l : Matrix (Fin n) (Fin n) R, IsUp I u ∧ IsDi I d ∧ IsLo I l ∧ g = u * d * l := by
  induction n with
  | zero =>
    intro g _
    exact ⟨1, 1, 1, ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩,
      ⟨fun i => i.elim0, fun i => i.elim0⟩, ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩,
      Subsingleton.elim _ _⟩
  | succ n ih =>
    intro g hg
    set A : Matrix (Fin n) (Fin n) R := fun i j => g i.castSucc j.castSucc with hA
    set c : Matrix (Fin n) (Fin 1) R := fun i _ => g i.castSucc (Fin.last n) with hc
    set r : Matrix (Fin 1) (Fin n) R := fun _ j => g (Fin.last n) j.castSucc with hr
    set s : R := g (Fin.last n) (Fin.last n) with hs
    have hs1 : s - 1 ∈ I := by simpa [hs] using hg (Fin.last n) (Fin.last n)
    have hsu : IsUnit s := by simpa using hI _ hs1
    obtain ⟨t, hst⟩ := hsu.exists_right_inv
    have hts : t * s = 1 := by rw [mul_comm]; exact hst
    have hcI : ∀ i k, c i k ∈ I := fun i k => by
      have := hg i.castSucc (Fin.last n)
      rw [Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne, sub_zero] at this
      exact this
    have hrI : ∀ k j, r k j ∈ I := fun k j => by
      have := hg (Fin.last n) j.castSucc
      rw [Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne', sub_zero] at this
      exact this
    set a : Matrix (Fin 1) (Fin 1) R := fun _ _ => s with ha
    set b : Matrix (Fin 1) (Fin 1) R := fun _ _ => t with hb
    have hab : a * b = 1 := by
      ext i j
      rw [Subsingleton.elim i j, Matrix.mul_apply, Matrix.one_apply_eq]
      simp only [Finset.univ_unique, Finset.sum_singleton]
      exact hst
    have hba : b * a = 1 := by
      ext i j
      rw [Subsingleton.elim i j, Matrix.mul_apply, Matrix.one_apply_eq]
      simp only [Finset.univ_unique, Finset.sum_singleton]
      exact hts
    have hS : ∀ i j, (A - c * b * r) i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I := by
      intro i j
      have h1 : A i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I := by
        have := hg i.castSucc j.castSucc
        simpa [hA, Matrix.one_apply] using this
      have h2 : (c * b * r) i j ∈ I := by
        simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton]
        exact I.mul_mem_right _ (I.mul_mem_right _ (hcI i default))
      have h3 : (A - c * b * r) i j - (1 : Matrix (Fin n) (Fin n) R) i j =
          (A i j - (1 : Matrix (Fin n) (Fin n) R) i j) - (c * b * r) i j := by
        simp only [Matrix.sub_apply]
        ring
      rw [h3]
      exact I.sub_mem h1 h2
    obtain ⟨u, d, l, hu, hd, hl, hudl⟩ := ih _ hS
    have hcb : ∀ i k, (c * b) i k ∈ I := fun i k => by
      simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton]
      exact I.mul_mem_right _ (hcI i default)
    have hbr : ∀ k j, (b * r) k j ∈ I := fun k j => by
      simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton]
      exact I.mul_mem_left _ (hrI default j)
    have haI : ∀ k k', a k k' - (1 : Matrix (Fin 1) (Fin 1) R) k k' ∈ I := fun k k' => by
      simpa [ha, Matrix.one_apply, Subsingleton.elim k k'] using hs1
    refine ⟨_, _, _, up_step hu hcb, di_step hd haI, lo_step hl hbr, ?_⟩
    have hblock : g.submatrix (ex n) (ex n) = fromBlocks A c r a := by
      ext i j
      rcases i with i | i <;> rcases j with j | j
      · rw [submatrix_apply, ex_inl, ex_inl]; rfl
      · rw [submatrix_apply, ex_inl, ex_inr]; rfl
      · rw [submatrix_apply, ex_inr, ex_inl]; rfl
      · rw [submatrix_apply, ex_inr, ex_inr]; rfl
    have hg' : g = (fromBlocks A c r a).submatrix (ex n).symm (ex n).symm := by
      rw [← hblock]
      simp
    rw [hg', fromBlocks_udl A c r a b hab hba u d l hudl]
    simp only [Matrix.submatrix_mul_equiv]

theorem iwahori_udl : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (n : ℕ)
    (ϖ : R) (m : ℕ), Irreducible ϖ → 1 ≤ m → ∀ g : Matrix (Fin n) (Fin n) R,
    (∀ i j, g i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) →
    ∃ (u d l : Matrix (Fin n) (Fin n) R),
      (∀ i j, u i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) ∧
      (∀ i j, d i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) ∧
      (∀ i j, l i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) ∧
      (∀ i j, j < i → u i j = 0) ∧ (∀ i, u i i = 1) ∧ (∀ i j, i ≠ j → d i j = 0) ∧
      (∀ i j, i < j → l i j = 0) ∧ (∀ i, l i i = 1) ∧ g = u * d * l := by
  intro R _ _ _ n ϖ m hϖ hm g hg
  have hmem : ϖ ^ m ∈ IsLocalRing.maximalIdeal R :=
    Ideal.pow_mem_of_mem _ ((IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit) m (by omega)
  have hle : Ideal.span {ϖ ^ m} ≤ IsLocalRing.maximalIdeal R :=
    (Ideal.span_singleton_le_iff_mem _).mpr hmem
  have hI : ∀ x ∈ Ideal.span {ϖ ^ m}, IsUnit (1 + x) := by
    intro x hx
    by_contra hnu
    have h1 : 1 + x ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h2 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      simpa using Ideal.sub_mem _ h1 (hle hx)
    exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal R).ne_top h2
  obtain ⟨u, d, l, hu, hd, hl, h⟩ := exists_udl_of_isUnit _ hI n g hg
  exact ⟨u, d, l, hu.1, hd.1, hl.1, hu.2.1, hu.2.2, hd.2, hl.2.1, hl.2.2, h⟩

end GlobalTheory.CompanionTheory.IwahoriUDL
