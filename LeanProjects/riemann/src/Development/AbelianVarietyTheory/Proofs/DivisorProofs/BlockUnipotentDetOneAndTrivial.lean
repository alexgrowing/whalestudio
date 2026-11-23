import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PutLinPack
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PutMulPut
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul.Hom

variable {R : Type} [CommRing R]

theorem put_entry (n o₁ o₂ : ℕ) {p q : ℕ} (X : Matrix (Fin p) (Fin q) R) (i j : Fin n) :
    put n o₁ o₂ X i j =
      if h : (o₁ ≤ i.val ∧ i.val < o₁ + p) ∧ (o₂ ≤ j.val ∧ j.val < o₂ + q) then
        X ⟨i.val - o₁, by omega⟩ ⟨j.val - o₂, by omega⟩ else 0 := rfl

theorem toGL_coe {n : ℕ} {M : Matrix (Fin n) (Fin n) R} (h : IsUnit M) :
    ((toGL M : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = M := by
  unfold toGL
  rw [dif_pos h]
  rfl

theorem det_one_add_put (n o₁ o₂ : ℕ) {p q : ℕ} (X : Matrix (Fin p) (Fin q) R)
    (hd : o₁ + p ≤ o₂ ∨ o₂ + q ≤ o₁) : (1 + put n o₁ o₂ X).det = 1 := by
  have hdiag : ∀ i : Fin n, (1 + put n o₁ o₂ X) i i = 1 := by
    intro i
    rw [Matrix.add_apply, Matrix.one_apply_eq, put_entry, dif_neg (by omega), add_zero]
  rcases hd with hd | hd
  · rw [Matrix.det_of_upperTriangular]
    · simp [hdiag]
    · intro i j hij
      have h' : j.val < i.val := hij
      rw [Matrix.add_apply, Matrix.one_apply_ne (show i ≠ j from fun e => by subst e; omega), put_entry, dif_neg (by omega), add_zero]
  · rw [Matrix.det_of_lowerTriangular]
    · simp [hdiag]
    · intro i j hij
      have h' : i.val < j.val := hij
      rw [Matrix.add_apply, Matrix.one_apply_ne (show i ≠ j from fun e => by subst e; omega), put_entry, dif_neg (by omega), add_zero]

theorem blk_mul (n o p : ℕ) (hp : o + p ≤ n) (A B : Matrix (Fin p) (Fin p) R) :
    (1 - eye R n o o p + put n o o A) * (1 - eye R n o o p + put n o o B) =
      1 - eye R n o o p + put n o o (A * B) := by
  have hm : ∀ X Y : Matrix (Fin p) (Fin p) R, put n o o X * put n o o Y = put n o o (X * Y) :=
    fun X Y => (put_mul_put R n o o o 0 p p p 0 X Y 0).1 hp
  unfold eye
  simp only [sub_mul, mul_sub, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, hm]
  abel

end GlobalTheory.GamMul.Hom

namespace GlobalTheory.GamMul.Hom

variable {R : Type} [CommRing R]

theorem uni_coe (n o₁ o₂ : ℕ) {p q : ℕ} (X : Matrix (Fin p) (Fin q) R) (hd : o₁ + p ≤ o₂ ∨ o₂ + q ≤ o₁) :
    ((uni n o₁ o₂ X : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 + put n o₁ o₂ X :=
  toGL_coe ((Matrix.isUnit_iff_isUnit_det _).2 (by rw [det_one_add_put n o₁ o₂ X hd]; exact isUnit_one))

theorem dg_coe (n o : ℕ) {p : ℕ} (g : GL (Fin p) R) (hp : o + p ≤ n) :
    ((dg n o g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 - eye R n o o p + put n o o g.val := by
  have h1 := blk_mul (R := R) n o p hp g.val g⁻¹.val
  have h2 := blk_mul (R := R) n o p hp g⁻¹.val g.val
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one] at h1
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one] at h2
  have e1 : (1 : Matrix (Fin n) (Fin n) R) - eye R n o o p + put n o o (1 : Matrix (Fin p) (Fin p) R) = 1 := by
    unfold eye; abel
  rw [e1] at h1 h2
  exact toGL_coe ⟨⟨_, _, h1, h2⟩, rfl⟩

theorem dg_one' (n o p : ℕ) : dg n o (1 : GL (Fin p) R) = 1 := by
  unfold dg
  rw [Units.val_one]
  have e1 : (1 : Matrix (Fin n) (Fin n) R) - eye R n o o p + put n o o (1 : Matrix (Fin p) (Fin p) R) = 1 := by
    unfold eye; abel
  rw [e1]
  exact Units.ext (toGL_coe isUnit_one)

theorem dg_mul' (n o : ℕ) {p : ℕ} (hp : o + p ≤ n) (g g' : GL (Fin p) R) :
    dg n o (g * g') = dg n o g * dg n o g' := by
  apply Units.ext
  rw [Units.val_mul, dg_coe n o _ hp, dg_coe n o _ hp, dg_coe n o _ hp, blk_mul n o p hp, Units.val_mul]

end GlobalTheory.GamMul.Hom

namespace GlobalTheory.GamMul.Hom

variable {R : Type} [CommRing R]

theorem dgM_in (n o p : ℕ) (A : Matrix (Fin p) (Fin p) R) (i j : Fin n) (hi : o ≤ i.val ∧ i.val < o + p)
    (hj : o ≤ j.val ∧ j.val < o + p) :
    (1 - eye R n o o p + put n o o A) i j = A ⟨i.val - o, by omega⟩ ⟨j.val - o, by omega⟩ := by
  unfold eye
  rw [Matrix.add_apply, Matrix.sub_apply, put_entry, put_entry, dif_pos ⟨hi, hj⟩, dif_pos ⟨hi, hj⟩]
  simp only [Matrix.one_apply, Fin.ext_iff]
  by_cases h : i.val = j.val
  · have h' : i.val - o = j.val - o := by omega
    simp [h, h']
  · have h' : i.val - o ≠ j.val - o := by omega
    simp [h, h']

theorem dgM_out (n o p : ℕ) (A : Matrix (Fin p) (Fin p) R) (i j : Fin n)
    (h : ¬((o ≤ i.val ∧ i.val < o + p) ∧ (o ≤ j.val ∧ j.val < o + p))) :
    (1 - eye R n o o p + put n o o A) i j = (1 : Matrix (Fin n) (Fin n) R) i j := by
  unfold eye
  rw [Matrix.add_apply, Matrix.sub_apply, put_entry, put_entry, dif_neg h, dif_neg h, sub_zero, add_zero]

theorem det_dg' (n o : ℕ) {p : ℕ} (hp : o + p ≤ n) (g : GL (Fin p) R) :
    GeneralLinearGroup.det (dg n o g) = GeneralLinearGroup.det g := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply, dg_coe n o g hp]
  let P : Fin n → Prop := fun i => o ≤ i.val ∧ i.val < o + p
  let f : {i : Fin n // P i} ≃ Fin p :=
    { toFun := fun i => ⟨i.1.val - o, by have := i.2; simp only [P] at this; omega⟩
      invFun := fun j => ⟨⟨o + j.val, by omega⟩, by simp only [P]; omega⟩
      left_inv := fun i => by
        have := i.2; simp only [P] at this
        apply Subtype.ext; apply Fin.ext; simp only; omega
      right_inv := fun j => by apply Fin.ext; simp only; omega }
  rw [Matrix.twoBlockTriangular_det _ P]
  · have h1 : toSquareBlockProp (1 - eye R n o o p + put n o o g.val) P = (g.val).submatrix f f := by
      ext i j
      have hi := i.2
      have hj := j.2
      simp only [P] at hi hj
      rw [toSquareBlockProp_def, Matrix.of_apply]
      rw [dgM_in n o p g.val i.1 j.1 hi hj]
      rfl
    have h2 : toSquareBlockProp (1 - eye R n o o p + put n o o g.val) (fun i => ¬P i) = 1 := by
      ext i j
      have hi := i.2
      rw [toSquareBlockProp_def, Matrix.of_apply]
      rw [dgM_out n o p g.val i.1 j.1 (fun h => hi h.1)]
      simp only [Matrix.one_apply, Subtype.ext_iff]
    rw [h1, h2, Matrix.det_submatrix_equiv_self, Matrix.det_one, mul_one]
  · intro i hi j hj
    rw [dgM_out n o p g.val i j (fun h => hi h.1), Matrix.one_apply_ne (by rintro rfl; exact hi hj)]

end GlobalTheory.GamMul.Hom

namespace GlobalTheory.GamMul.Hom

variable {R : Type} [CommRing R]

theorem dg_mul_dg_eq_emb₂ (n p q : ℕ) (h : p + q = n) (a : GL (Fin p) R) (b : GL (Fin q) R) :
    dg n 0 a * dg n p b = emb₂ R (stdSum h) (a, b) := by
  apply Units.ext
  rw [Units.val_mul, dg_coe n 0 a (by omega), dg_coe n p b (by omega), val_emb₂]
  have hz : ∀ (X : Matrix (Fin p) (Fin p) R) (Z : Matrix (Fin q) (Fin q) R),
      put n 0 0 X * put n p p Z = 0 :=
    fun X Z => (put_mul_put R n 0 0 p p p p q q X 0 Z).2 (Or.inl (by omega))
  have hsum : put n 0 0 (1 : Matrix (Fin p) (Fin p) R) + put n p p (1 : Matrix (Fin q) (Fin q) R) = 1 := by
    have h1 := (put_lin_pack R n 0 0 p q).2.2.2.2.1
    have h2 := (put_lin_pack R n 0 0 p q).2.2.2.2.2.1
    simp only [zero_add] at h1
    rw [h] at h1
    rw [← h2, h1]
    rfl
  have key : (1 - eye R n 0 0 p + put n 0 0 a.val) * (1 - eye R n p p q + put n p p b.val) =
      put n 0 0 a.val + put n p p b.val := by
    unfold eye
    simp only [sub_mul, mul_sub, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, hz]
    rw [← hsum]
    abel
  rw [key]
  ext i j
  obtain ⟨i, rfl⟩ := (stdSum h).surjective i
  obtain ⟨j, rfl⟩ := (stdSum h).surjective j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    Matrix.add_apply, put_entry, put_entry]
  rcases i with i | i <;> rcases j with j | j
  · have hi := i.2
    have hj := j.2
    rw [dif_pos (by simp only [stdSum_inl]; omega), dif_neg (by simp only [stdSum_inl]; omega), add_zero,
      fromBlocks_apply₁₁]
    congr 1 <;> apply Fin.ext <;> simp
  · have hi := i.2
    rw [dif_neg (by simp only [stdSum_inl, stdSum_inr]; omega), dif_neg (by simp only [stdSum_inl, stdSum_inr]; omega), add_zero,
      fromBlocks_apply₁₂, Matrix.zero_apply]
  · have hj := j.2
    rw [dif_neg (by simp only [stdSum_inl, stdSum_inr]; omega), dif_neg (by simp only [stdSum_inl, stdSum_inr]; omega), add_zero,
      fromBlocks_apply₂₁, Matrix.zero_apply]
  · have hi := i.2
    have hj := j.2
    rw [dif_neg (by simp only [stdSum_inr]; omega), dif_pos (by simp only [stdSum_inr]; omega), zero_add,
      fromBlocks_apply₂₂]
    show _ = (b : Matrix (Fin q) (Fin q) R) i j
    exact congrArg₂ (fun x y => (b : Matrix (Fin q) (Fin q) R) x y) (Fin.ext (by simp)) (Fin.ext (by simp))

theorem shuf_zero' (n : ℕ) : shuf R n 0 = 1 := by
  unfold shuf
  have h1 := (put_lin_pack R n 0 0 0 0).2.2.2.2.2.1
  have h2 := (put_lin_pack R n n 0 0 0).2.2.2.2.2.2.1 (1 : Matrix (Fin 0) (Fin 0) R) (Or.inl rfl)
  rw [Nat.sub_zero]
  change toGL (eye R n 0 0 n + put n n 0 (1 : Matrix (Fin 0) (Fin 0) R)) = 1
  rw [h1, h2, add_zero]
  exact Units.ext (toGL_coe isUnit_one)

theorem dg_zero_self (n : ℕ) (g : GL (Fin n) R) : dg n 0 g = g := by
  unfold dg
  rw [(put_lin_pack R n 0 0 0 0).2.2.2.2.2.1, (put_lin_pack R n 0 0 0 0).2.2.2.2.2.2.2, sub_self, zero_add]
  exact toGL_val g

end GlobalTheory.GamMul.Hom

namespace GlobalTheory.GamMul

theorem uni_dg_hom : ∀ (R : Type) [CommRing R] (n o₁ o₂ p q : ℕ), ((o₁ + p ≤ o₂ ∨ o₂ + q ≤ o₁) → (∀ X Y : Matrix (Fin p) (Fin q) R, uni n o₁ o₂ (X + Y) = uni n o₁ o₂ X * uni n o₁ o₂ Y) ∧ (∀ X : Matrix (Fin p) (Fin q) R, GeneralLinearGroup.det (uni n o₁ o₂ X) = 1)) ∧ uni n o₁ o₂ (0 : Matrix (Fin p) (Fin q) R) = 1 ∧ (∀ X : Matrix (Fin p) (Fin q) R, (p = 0 ∨ q = 0) → uni n o₁ o₂ X = 1) ∧ dg n o₁ (1 : GL (Fin p) R) = 1 ∧ (o₁ + p ≤ n → (∀ g g' : GL (Fin p) R, dg n o₁ (g * g') = dg n o₁ g * dg n o₁ g') ∧ ∀ g : GL (Fin p) R, GeneralLinearGroup.det (dg n o₁ g) = GeneralLinearGroup.det g) ∧ (∀ (h : p + q = n) (a : GL (Fin p) R) (b : GL (Fin q) R), dg n 0 a * dg n p b = emb₂ R (stdSum h) (a, b)) ∧ shuf R n 0 = 1 ∧ (∀ g : GL (Fin n) R, dg n 0 g = g) := by
  intro R _ n o₁ o₂ p q
  have hone : ∀ M : Matrix (Fin n) (Fin n) R, M = 0 → toGL (1 + M) = 1 := by
    intro M hM
    rw [hM, add_zero]
    exact Units.ext (Hom.toGL_coe isUnit_one)
  refine ⟨fun hd => ⟨fun X Y => ?_, fun X => ?_⟩, ?_, fun X hX => ?_, Hom.dg_one' n o₁ p,
    fun hp => ⟨fun g g' => Hom.dg_mul' n o₁ hp g g', fun g => Hom.det_dg' n o₁ hp g⟩,
    fun h a b => Hom.dg_mul_dg_eq_emb₂ n p q h a b, Hom.shuf_zero' n, Hom.dg_zero_self n⟩
  · apply Units.ext
    rw [Units.val_mul, Hom.uni_coe n o₁ o₂ _ hd, Hom.uni_coe n o₁ o₂ _ hd, Hom.uni_coe n o₁ o₂ _ hd,
      (put_lin_pack R n o₁ o₂ p q).1, add_mul, mul_add, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
      (put_mul_put R n o₁ o₂ o₁ o₂ p q q p X 0 Y).2 (hd.symm.imp id id)]
    abel
  · apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, Hom.uni_coe n o₁ o₂ _ hd, Hom.det_one_add_put n o₁ o₂ X hd, Units.val_one]
  · exact hone _ (put_lin_pack R n o₁ o₂ p q).2.2.1
  · exact hone _ ((put_lin_pack R n o₁ o₂ p q).2.2.2.2.2.2.1 X hX)

end GlobalTheory.GamMul
