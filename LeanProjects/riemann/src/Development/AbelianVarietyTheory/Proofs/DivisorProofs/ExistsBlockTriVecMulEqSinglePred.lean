import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigCongr

noncomputable section

namespace GlobalTheory.FinGL.LeviWh

open Formalism.L2.DIV Module Matrix

theorem eq_one_off_mul {F : Type} [Field F] {r : ℕ} (S : Fin r → Prop) (M N : Matrix (Fin r) (Fin r) F)
    (hM : ∀ i j, ¬ (S i ∧ S j) → M i j = (1 : Matrix (Fin r) (Fin r) F) i j)
    (hN : ∀ i j, ¬ (S i ∧ S j) → N i j = (1 : Matrix (Fin r) (Fin r) F) i j) :
    ∀ i j, ¬ (S i ∧ S j) → (M * N) i j = (1 : Matrix (Fin r) (Fin r) F) i j := by
  intro i j hij
  by_cases hi : S i
  · have hj : ¬ S j := fun h => hij ⟨hi, h⟩
    have e : (M * N) i j = (M * (1 : Matrix (Fin r) (Fin r) F)) i j := by
      simp only [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun a _ => by rw [hN a j fun h => hj h.2]
    rw [e, Matrix.mul_one, hM i j hij]
  · have e : (M * N) i j = ((1 : Matrix (Fin r) (Fin r) F) * N) i j := by
      simp only [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun a _ => by rw [hM i a fun h => hi h.1]
    rw [e, Matrix.one_mul, hN i j hij]

theorem exists_gl_vecMul_eq_single_of_ne {F : Type} [Field F] {r : ℕ} (S : Fin r → Prop) (c : Fin r) (hc : S c)
    (l : Fin r → F) (hl : l c ≠ 0) (hS : ∀ i, l i ≠ 0 → S i) :
    ∃ h : GL (Fin r) F, (∀ i j, ¬ (S i ∧ S j) → (h : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) ∧
      Matrix.vecMul l (h : Matrix (Fin r) (Fin r) F) = Pi.single c 1 := by
  set e : Fin r → F := Pi.single c 1 with he
  set A : Matrix (Fin r) (Fin r) F := vecMulVec e (l - e) with hA
  have hd : (l - e) ⬝ᵥ e = l c - 1 := by simp [he]
  have hAA : A * A = (l c - 1) • A := by
    rw [hA, vecMulVec_mul_vecMulVec, hd, vecMulVec_smul]
  have h1 : (1 - (l c)⁻¹ • A) * (1 + A) = 1 := by
    rw [sub_mul, one_mul, smul_mul_assoc, mul_add, mul_one, hAA]
    have : A + (l c - 1) • A = l c • A := by rw [sub_smul, one_smul]; abel
    rw [this, smul_smul, inv_mul_cancel₀ hl, one_smul]; abel
  refine ⟨⟨1 - (l c)⁻¹ • A, 1 + A, h1, mul_eq_one_comm.mp h1⟩, ?_, ?_⟩
  · intro i j hij
    have : A i j = 0 := by
      rw [hA, vecMulVec_apply]
      by_cases hi : i = c
      · have hj : ¬ S j := fun h => hij ⟨hi ▸ hc, h⟩
        have hlj : l j = 0 := by
          by_contra h
          exact hj (hS j h)
        have hjc : j ≠ c := fun h => hj (h ▸ hc)
        simp [he, hlj, hjc]
      · simp [he, hi]
    simp [this]
  · have hv : Matrix.vecMul l A = l c • (l - e) := by
      rw [hA, vecMul_vecMulVec]
      simp [he]
    show Matrix.vecMul l (1 - (l c)⁻¹ • A) = e
    rw [vecMul_sub, vecMul_one, vecMul_smul, hv, smul_smul, inv_mul_cancel₀ hl, one_smul]
    abel

theorem exists_gl_vecMul_eq_single {F : Type} [Field F] {r : ℕ} (S : Fin r → Prop) (c : Fin r) (hc : S c)
    (l : Fin r → F) (hl : l ≠ 0) (hS : ∀ i, l i ≠ 0 → S i) :
    ∃ h : GL (Fin r) F, (∀ i j, ¬ (S i ∧ S j) → (h : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) ∧
      Matrix.vecMul l (h : Matrix (Fin r) (Fin r) F) = Pi.single c 1 := by
  by_cases hlc : l c = 0
  swap
  · exact exists_gl_vecMul_eq_single_of_ne S c hc l hlc hS
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hl
  have ha : l a ≠ 0 := ha
  have hac : a ≠ c := fun h => ha (h ▸ hlc)
  have h1 : transvection a c (1 : F) * transvection a c (-1 : F) = 1 := by
    rw [transvection_mul_transvection_same a c hac, add_neg_cancel, transvection_zero]
  let t : GL (Fin r) F := ⟨transvection a c 1, transvection a c (-1), h1, mul_eq_one_comm.mp h1⟩
  have hv : ∀ j, Matrix.vecMul l (transvection a c (1 : F)) j = l j + if j = c then l a else 0 := by
    intro j
    rw [transvection, vecMul_add, vecMul_one, Pi.add_apply]
    congr 1
    by_cases hj : j = c
    · subst hj
      simp [vecMul, dotProduct, Matrix.single_apply]
    · simp [vecMul, dotProduct, Matrix.single_apply, hj, Ne.symm hj]
  obtain ⟨h, hh1, hh2⟩ := exists_gl_vecMul_eq_single_of_ne S c hc (Matrix.vecMul l (transvection a c (1 : F)))
    (by rw [hv]; simpa [hlc] using ha)
    (by
      intro i hi
      by_cases hic : i = c
      · exact hic ▸ hc
      · rw [hv] at hi
        exact hS i (by simpa [hic] using hi))
  refine ⟨t * h, ?_, ?_⟩
  · refine eq_one_off_mul S (transvection a c (1 : F)) _ ?_ hh1
    intro i j hij
    have : ¬ (a = i ∧ c = j) := fun h => hij ⟨h.1 ▸ hS a ha, h.2 ▸ hc⟩
    simp [transvection, Matrix.single_apply, this]
  · rw [← hh2, vecMul_vecMul]
    rfl

theorem exists_blockTri_vecMul_eq_single : ∀ (F : Type) [Field F] (r : ℕ) (b : Fin r → ℕ), Monotone b → ∀ (k k' : Fin r), k'.val + 1 = k.val → ∀ l : Fin r → F, l ≠ 0 → (∀ i, l i ≠ 0 → i < k ∧ b i = b k) → ∃ h : blockTri (κ := F) b, (∀ i j, ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → i < k ∧ j < k) ∧ Matrix.vecMul l ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = Pi.single k' 1 := by
  intro F _ r b hb k k' hk l hl hS
  have hk' : k' < k ∧ b k' = b k := by
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hl
    obtain ⟨h1, h2⟩ := hS a ha
    have h3 : k' < k := by rw [Fin.lt_def]; omega
    have h4 : a ≤ k' := by rw [Fin.lt_def] at h1; rw [Fin.le_def]; omega
    exact ⟨h3, le_antisymm (hb h3.le) (h2 ▸ hb h4)⟩
  obtain ⟨h, h1, h2⟩ := exists_gl_vecMul_eq_single (fun i => i < k ∧ b i = b k) k' hk' l hl hS
  refine ⟨⟨h, ?_⟩, ?_, h2⟩
  · have : (h : Matrix (Fin r) (Fin r) F).BlockTriangular b := by
      intro i j hij
      rw [h1 i j (fun hh => by rw [hh.1.2, hh.2.2] at hij; exact lt_irrefl _ hij)]
      exact Matrix.one_apply_ne (fun e => by rw [e] at hij; exact lt_irrefl _ hij)
    exact this
  · intro i j hij
    by_contra hn
    exact hij (h1 i j fun hh => hn ⟨hh.1.1, hh.2.1⟩)

end GlobalTheory.FinGL.LeviWh
