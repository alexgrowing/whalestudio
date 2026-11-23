import Mathlib

open Matrix

namespace GlobalTheory.CompanionTheory.GenericLU

theorem affine_form_ne_zero {K L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (a : K) (b : Fin n → K) (x : Fin n → L) (hx : AlgebraicIndependent K x)
    (hab : a ≠ 0 ∨ ∃ j, b j ≠ 0) :
    algebraMap K L a + ∑ j, algebraMap K L (b j) * x j ≠ 0 := by
  classical
  intro h
  let P : MvPolynomial (Fin n) K :=
    MvPolynomial.C a + ∑ j, MvPolynomial.C (b j) * MvPolynomial.X j
  have hP : MvPolynomial.aeval x P = 0 := by
    simpa [P, map_add, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X] using h
  have hP0 : P = 0 := by
    have := (injective_iff_map_eq_zero (MvPolynomial.aeval x : MvPolynomial (Fin n) K →ₐ[K] L)).mp hx
    exact this P hP
  rcases hab with ha | ⟨j, hj⟩
  · apply ha
    have := congrArg (MvPolynomial.coeff 0) hP0
    simpa [P, MvPolynomial.coeff_add, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_C, MvPolynomial.coeff_X'] using this
  · apply hj
    have := congrArg (MvPolynomial.coeff (Finsupp.single j 1)) hP0
    have hne : (0 : Fin n →₀ ℕ) ≠ Finsupp.single j 1 :=
      (Finsupp.single_ne_zero.mpr one_ne_zero).symm
    simpa [P, hne, MvPolynomial.coeff_add, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_C, MvPolynomial.coeff_X', Finsupp.single_left_inj, Finsupp.single_eq_single_iff] using this

theorem schur_det_ne_zero {F : Type} [Field F] {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (x : Fin n → F) (hA : A.det ≠ 0) (q : Fin (n + 1) → F)
    (hq : ∀ i, q i = A i 0 + ∑ k, A i k.succ * x k) (h0 : q 0 ≠ 0) :
    (Matrix.of fun i j : Fin n => A i.succ j.succ - q i.succ / q 0 * A 0 j.succ).det ≠ 0 := by
  intro hdet
  obtain ⟨y, hy, hSy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set t : F := -(∑ j, A 0 j.succ * y j) / q 0 with ht
  apply hA
  refine Matrix.exists_mulVec_eq_zero_iff.mp
    ⟨Fin.cons t (fun k => y k + t * x k), ?_, ?_⟩
  · intro hz
    have h1 : t = 0 := by simpa using congrFun hz 0
    apply hy
    funext k
    have := congrFun hz k.succ
    simpa [h1] using this
  · have key : ∀ i, (A *ᵥ (Fin.cons t (fun k => y k + t * x k) : Fin (n + 1) → F)) i
        = t * q i + ∑ k, A i k.succ * y k := by
      intro i
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hq,
        mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      have : ∀ k, A i k.succ * (t * x k) = t * (A i k.succ * x k) := fun k => by ring
      simp only [this]
      ring
    funext i
    rw [key]
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [ht, Pi.zero_apply]
      field_simp
      ring
    · have h := congrFun hSy i
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply, sub_mul,
        Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum] at h
      simp only [ht, Pi.zero_apply]
      field_simp at h ⊢
      linear_combination h

theorem lu_step {L : Type} [Field L] {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) L)
    (hM : M 0 0 ≠ 0) (v' w' : Matrix (Fin n) (Fin n) L)
    (hsch : ∀ i j, M i.succ j.succ - M i.succ 0 / M 0 0 * M 0 j.succ = (v' * w') i j)
    (h1 : ∀ k, v' k k = 1) (h2 : ∀ l k, l < k → v' l k = 0)
    (h3 : ∀ l k, k < l → w' l k = 0) (h4 : ∀ k, w' k k ≠ 0) :
    ∃ v w : Matrix (Fin (n + 1)) (Fin (n + 1)) L, M = v * w ∧ (∀ k, v k k = 1) ∧
      (∀ l k, l < k → v l k = 0) ∧ (∀ l k, k < l → w l k = 0) ∧ ∀ k, w k k ≠ 0 := by
  let v : Matrix (Fin (n + 1)) (Fin (n + 1)) L := fun i j =>
    Fin.cases (Fin.cases 1 (fun _ => 0) j)
      (fun i' => Fin.cases (M i'.succ 0 / M 0 0) (fun j' => v' i' j') j) i
  let w : Matrix (Fin (n + 1)) (Fin (n + 1)) L := fun i j =>
    Fin.cases (Fin.cases (M 0 0) (fun j' => M 0 j'.succ) j)
      (fun i' => Fin.cases 0 (fun j' => w' i' j') j) i
  have v00 : v 0 0 = 1 := rfl
  have v0s : ∀ j, v 0 (Fin.succ j) = 0 := fun _ => rfl
  have vs0 : ∀ i, v (Fin.succ i) 0 = M i.succ 0 / M 0 0 := fun _ => rfl
  have vss : ∀ i j, v (Fin.succ i) (Fin.succ j) = v' i j := fun _ _ => rfl
  have w00 : w 0 0 = M 0 0 := rfl
  have w0s : ∀ j, w 0 (Fin.succ j) = M 0 j.succ := fun _ => rfl
  have ws0 : ∀ i, w (Fin.succ i) 0 = 0 := fun _ => rfl
  have wss : ∀ i j, w (Fin.succ i) (Fin.succ j) = w' i j := fun _ _ => rfl
  refine ⟨v, w, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [v00, v0s, w00]
    · simp [v00, v0s, w0s]
    · simp [vs0, vss, w00, ws0]
      field_simp
    · have := hsch i j
      rw [Matrix.mul_apply] at this
      simp only [vs0, vss, w0s, wss]
      rw [← this]
      ring
  · intro k
    refine Fin.cases ?_ (fun k => ?_) k
    · exact v00
    · rw [vss]; exact h1 k
  · intro l k
    refine Fin.cases ?_ (fun l => ?_) l <;> refine Fin.cases ?_ (fun k => ?_) k
    · intro h; exact absurd h (lt_irrefl _)
    · intro _; exact v0s k
    · intro h; exact absurd h (Fin.not_lt_zero _)
    · intro h; rw [vss]; exact h2 l k (Fin.succ_lt_succ_iff.mp h)
  · intro l k
    refine Fin.cases ?_ (fun l => ?_) l <;> refine Fin.cases ?_ (fun k => ?_) k
    · intro h; exact absurd h (lt_irrefl _)
    · intro h; exact absurd h (Fin.not_lt_zero _)
    · intro _; exact ws0 l
    · intro h; rw [wss]; exact h3 l k (Fin.succ_lt_succ_iff.mp h)
  · intro k
    refine Fin.cases ?_ (fun k => ?_) k
    · rw [w00]; exact hM
    · rw [wss]; exact h4 k

theorem generic_lu_decomposition_exists (n : ℕ) : ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    (A : Matrix (Fin n) (Fin n) K) (u : Matrix (Fin n) (Fin n) L), A.det ≠ 0 →
    (∀ k, u k k = 1) → (∀ l k, l < k → u l k = 0) →
    AlgebraicIndependent K (fun q : {lk : Fin n × Fin n // lk.2 < lk.1} => u q.1.1 q.1.2) →
    ∃ v w : Matrix (Fin n) (Fin n) L, A.map (algebraMap K L) * u = v * w ∧ (∀ k, v k k = 1) ∧
      (∀ l k, l < k → v l k = 0) ∧ (∀ l k, k < l → w l k = 0) ∧ ∀ k, w k k ≠ 0 := by
  induction n with
  | zero =>
    intro K L _ _ _ A u _ _ _ _
    exact ⟨0, 0, Subsingleton.elim _ _, fun k => k.elim0, fun l => l.elim0, fun l => l.elim0,
      fun k => k.elim0⟩
  | succ n ih =>
    intro K L _ _ _ A u hA hdiag hup hind
    let x : Fin n → L := fun i => u i.succ 0
    let u' : Matrix (Fin n) (Fin n) L := fun i j => u i.succ j.succ
    let y : {lk : Fin n × Fin n // lk.2 < lk.1} → L := fun q => u' q.1.1 q.1.2
    let idx : {lk : Fin n × Fin n // lk.2 < lk.1} ⊕ Fin n →
        {lk : Fin (n + 1) × Fin (n + 1) // lk.2 < lk.1} :=
      Sum.elim (fun q => ⟨(q.1.1.succ, q.1.2.succ), Fin.succ_lt_succ_iff.mpr q.2⟩)
        (fun i => ⟨(i.succ, 0), Fin.succ_pos i⟩)
    have hidx : Function.Injective idx := by
      rintro (s | i) (s' | i') hh
      · have e : (s.1.1.succ, s.1.2.succ) = (s'.1.1.succ, s'.1.2.succ) :=
          congrArg Subtype.val hh
        exact congrArg Sum.inl (Subtype.ext (Prod.ext
          (Fin.succ_injective _ (congrArg Prod.fst e))
          (Fin.succ_injective _ (congrArg Prod.snd e))))
      · have e : (s.1.1.succ, s.1.2.succ) = (i'.succ, (0 : Fin (n + 1))) :=
          congrArg Subtype.val hh
        exact absurd (congrArg Prod.snd e) (Fin.succ_ne_zero _)
      · have e : (i.succ, (0 : Fin (n + 1))) = (s'.1.1.succ, s'.1.2.succ) :=
          congrArg Subtype.val hh
        exact absurd (congrArg Prod.snd e).symm (Fin.succ_ne_zero _)
      · have e : (i.succ, (0 : Fin (n + 1))) = (i'.succ, (0 : Fin (n + 1))) :=
          congrArg Subtype.val hh
        exact congrArg Sum.inr (Fin.succ_injective _ (congrArg Prod.fst e))
    have hsum : AlgebraicIndependent K (Sum.elim y x) := by
      have := hind.comp idx hidx
      convert this using 1
      funext s
      rcases s with q | i <;> rfl
    obtain ⟨hx, hy⟩ := AlgebraicIndependent.sumElim_iff.mp hsum
    have hy' : AlgebraicIndependent (IntermediateField.adjoin K (Set.range x)) y :=
      IntermediateField.algebraicIndependent_adjoin_iff.mpr hy
    let K₁ := IntermediateField.adjoin K (Set.range x)
    let xs : Fin n → K₁ := fun i => ⟨x i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
    let A₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) K₁ := A.map (algebraMap K K₁)
    let q : Fin (n + 1) → K₁ := fun i => A₁ i 0 + ∑ k, A₁ i k.succ * xs k
    have hA₁ : A₁.det ≠ 0 := by
      have : A₁.det = algebraMap K K₁ A.det := by
        simpa [A₁] using (RingHom.map_det (algebraMap K K₁) A).symm
      rw [this]
      exact (map_ne_zero _).mpr hA
    let M : Matrix (Fin (n + 1)) (Fin (n + 1)) L := A.map (algebraMap K L) * u
    have hcoe : ∀ i j, algebraMap K₁ L (A₁ i j) = algebraMap K L (A i j) := fun i j =>
      (IsScalarTower.algebraMap_apply K K₁ L (A i j)).symm
    have hxs : ∀ k, algebraMap K₁ L (xs k) = x k := fun _ => rfl
    have hM0 : ∀ i, M i 0 = algebraMap K₁ L (q i) := by
      intro i
      simp only [M, q, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.map_apply, hdiag, map_add,
        map_sum, map_mul, hcoe, hxs, mul_one]
      rfl
    have hMs : ∀ i j, M i j.succ = ∑ k, algebraMap K L (A i k.succ) * u' k j := by
      intro i j
      simp only [M, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.map_apply]
      rw [hup 0 j.succ (Fin.succ_pos j)]
      simp [u']
    have hp : M 0 0 ≠ 0 := by
      have hne : A 0 0 ≠ 0 ∨ ∃ j, A 0 (Fin.succ j) ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        apply hA
        apply Matrix.det_eq_zero_of_row_eq_zero 0
        intro j
        refine Fin.cases hcon.1 hcon.2 j
      have := affine_form_ne_zero (A 0 0) (fun j => A 0 j.succ) x hx hne
      have h2 : M 0 0 = algebraMap K L (A 0 0) + ∑ j, algebraMap K L (A 0 j.succ) * x j := by
        simp only [M, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.map_apply, hdiag, mul_one]
        rfl
      rwa [h2]
    have hq0 : q 0 ≠ 0 := by
      intro h
      apply hp
      rw [hM0, h, map_zero]
    let S : Matrix (Fin n) (Fin n) K₁ :=
      Matrix.of fun i j : Fin n => A₁ i.succ j.succ - q i.succ / q 0 * A₁ 0 j.succ
    have hS : S.det ≠ 0 := schur_det_ne_zero A₁ xs hA₁ q (fun _ => rfl) hq0
    obtain ⟨v', w', hvw, h1, h2, h3, h4⟩ := ih K₁ L S u' hS (fun k => hdiag k.succ)
      (fun l k h => hup l.succ k.succ (Fin.succ_lt_succ_iff.mpr h)) hy'
    refine lu_step M hp v' w' ?_ h1 h2 h3 h4
    intro i j
    rw [← hvw, Matrix.mul_apply, hMs, hMs, hM0, hM0, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [S, Matrix.map_apply, Matrix.of_apply, map_sub, map_mul, map_div₀, hcoe]
    ring

theorem generic_lu : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (n : ℕ)
    (A : Matrix (Fin n) (Fin n) K) (u : Matrix (Fin n) (Fin n) L), A.det ≠ 0 →
    (∀ k, u k k = 1) → (∀ l k, l < k → u l k = 0) →
    AlgebraicIndependent K (fun q : {lk : Fin n × Fin n // lk.2 < lk.1} => u q.1.1 q.1.2) →
    ∃ v w : Matrix (Fin n) (Fin n) L, A.map (algebraMap K L) * u = v * w ∧ (∀ k, v k k = 1) ∧
      (∀ l k, l < k → v l k = 0) ∧ (∀ l k, k < l → w l k = 0) ∧ ∀ k, w k k ≠ 0 := by
  intro K L _ _ _ n
  exact generic_lu_decomposition_exists n K L

end GlobalTheory.CompanionTheory.GenericLU
