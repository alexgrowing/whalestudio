import Mathlib
import Formalism.FormalDegreeBessel.StatementG

open Matrix

noncomputable section

namespace GlobalTheory.LeadingMinorInv

open Formalism.QuantumDeterminants

def UpUni {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ i j, j < i → U i j = 0) ∧ ∀ i, U i i = 1

lemma minor_mul {n l : ℕ} (hl : l ≤ n) (A U : Matrix (Fin n) (Fin n) ℂ) (hU : UpUni U) :
    ((A * U).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (A.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  have hsub : (A * U).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      A.submatrix (Fin.castLE hl) (Fin.castLE hl) * U.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    apply Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl)
    · intro b hb
      have hjb : Fin.castLE hl j < b := by
        rw [Fin.lt_def]
        show j.val < b.val
        by_contra hc
        have := j.isLt
        exact hb ⟨⟨b.val, by omega⟩, Fin.ext rfl⟩
      rw [hU.1 b _ hjb, mul_zero]
    · intro a
      rfl
  have hdet : (U.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular]
    · simp [Matrix.submatrix_apply, hU.2]
    · intro i j hij
      simp only [Matrix.submatrix_apply]
      apply hU.1
      rw [Fin.lt_def] at hij ⊢
      exact hij
  rw [hsub, Matrix.det_mul, hdet, mul_one]

lemma minor_mul_left {n l : ℕ} (hl : l ≤ n) (A U : Matrix (Fin n) (Fin n) ℂ) (hU : UpUni U) :
    ((Uᴴ * A).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (A.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  have e : Uᴴ * A = (Aᴴ * U)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [e, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose, minor_mul hl _ _ hU,
    ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose, star_star]

def flagMat (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ := Matrix.of fun i a => fvec k r z a i

lemma mul_flagMat (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i) (b) :
    (g * flagMat k r z) i b = (g *ᵥ fvec k r z b) i := rfl

lemma zhat_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Zhat k r z z' g = (flagMat k r z)ᴴ * (Hpk k r * (g * flagMat k r z')) := by
  ext a b
  simp only [Zhat, herm, Matrix.mul_apply, Matrix.conjTranspose_apply, flagMat, Matrix.of_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply]

lemma exists_N (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hm : m ∈ Nset k r) :
    ∃ U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, UpUni U ∧ m * flagMat k r z = flagMat k r z * U := by
  simp only [Nset, Set.mem_setOf_eq] at hm
  obtain ⟨-, hm2, hm3⟩ := hm
  have key : ∀ (a : Fin (r + 1)) (i : Fin (2 * r + k + 1)),
      (m *ᵥ fvec k r z a) i =
        fvec k r z a i + if i.val < a.val then (m *ᵥ fvec k r z a) i else 0 := by
    intro a i
    have ha := a.isLt
    by_cases hia : i.val < a.val
    · rw [if_pos hia]
      suffices h0 : fvec k r z a i = 0 by rw [h0, zero_add]
      by_cases har : a.val < r
      · simp only [fvec, dif_pos har, bvec]
        rw [Pi.single_apply, if_neg]
        intro he
        have h1 := congrArg Fin.val he
        simp [eI] at h1
        omega
      · simp only [fvec, dif_neg har]
        exact hz i (Or.inl (by omega))
    · rw [if_neg hia, add_zero]
      by_cases har : a.val < r
      · simp only [fvec, dif_pos har, bvec]
        simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
        exact hm2 ⟨a.val, har⟩ i (by show a.val ≤ i.val; omega)
      · simp only [fvec, dif_neg har]
        have hterm : ∀ j, m i j * z j = if i = j then z j else 0 := by
          intro j
          by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
          · rw [hm3 i j hj.1 hj.2 (by omega)]
            split_ifs <;> simp
          · rw [hz j (by omega)]
            simp
        simp only [Matrix.mulVec, dotProduct, hterm, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine ⟨Matrix.of fun b a => (if b = a then 1 else 0) +
      (if hba : b.val < a.val then
        (m *ᵥ fvec k r z a) (eI k r ⟨b.val, by have := a.isLt; omega⟩) else 0), ⟨?_, ?_⟩, ?_⟩
  · intro i j hij
    have h1 : i ≠ j := hij.ne'
    have h2 : ¬ i < j := by rw [Fin.lt_def] at hij ⊢; omega
    simp [h1, h2]
  · intro i
    simp
  · ext i a
    rw [mul_flagMat, Matrix.mul_apply]
    simp only [flagMat, Matrix.of_apply, mul_add, Finset.sum_add_distrib, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [key a i]
    congr 1
    have ha := a.isLt
    by_cases hia : i.val < a.val
    · have hir : i.val < r := by omega
      rw [if_pos hia, Finset.sum_eq_single (⟨i.val, by omega⟩ : Fin (r + 1))]
      · have he : eI k r ⟨i.val, hir⟩ = i := Fin.ext rfl
        simp [fvec, hir, hia, he, bvec]
      · intro b _ hb
        split_ifs with hba
        · have hbr : b.val < r := by omega
          have hne : i ≠ eI k r ⟨b.val, hbr⟩ := by
            intro he
            apply hb
            ext
            exact (congrArg Fin.val he).symm
          simp [fvec, hbr, bvec, Pi.single_apply, hne]
        · simp
      · simp
    · rw [if_neg hia]
      symm
      apply Finset.sum_eq_zero
      intro b _
      split_ifs with hba
      · have hbr : b.val < r := by omega
        have hne : i ≠ eI k r ⟨b.val, hbr⟩ := by
          intro he
          apply hia
          rw [he]
          exact hba
        simp [fvec, hbr, bvec, Pi.single_apply, hne]
      · simp

lemma exists_S (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hs : s ∈ Sset k r z) :
    sᴴ * Hpk k r * s = Hpk k r ∧ ∃ U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, UpUni U ∧ s * flagMat k r z = flagMat k r z * U := by
  simp only [Sset, Set.mem_setOf_eq] at hs
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  obtain ⟨U, hU, hmF⟩ := exists_N k r z hz m hm
  simp only [UWset, Set.mem_setOf_eq] at hh
  obtain ⟨hhU, hfix, hhz⟩ := hh
  have hmU : mᴴ * Hpk k r * m = Hpk k r := by
    simp only [Nset, Set.mem_setOf_eq] at hm
    exact hm.1
  have hhU' : hᴴ * Hpk k r * h = Hpk k r := hhU
  refine ⟨?_, U, hU, ?_⟩
  · calc (h * m)ᴴ * Hpk k r * (h * m) = mᴴ * (hᴴ * Hpk k r * h) * m := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r := by rw [hhU', hmU]
  · have hF : h * flagMat k r z = flagMat k r z := by
      ext i b
      rw [mul_flagMat]
      simp only [flagMat, Matrix.of_apply]
      by_cases hb : b.val < r
      · simp only [fvec, dif_pos hb]
        rw [(hfix ⟨b.val, hb⟩).1]
      · simp only [fvec, dif_neg hb]
        rw [hhz]
    rw [Matrix.mul_assoc, hmF, ← Matrix.mul_assoc, hF]

end GlobalTheory.LeadingMinorInv

namespace GlobalTheory

open Formalism.QuantumDeterminants LeadingMinorInv

end GlobalTheory
