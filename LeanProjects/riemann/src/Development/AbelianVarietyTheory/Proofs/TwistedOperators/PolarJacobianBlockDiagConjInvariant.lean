import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY

noncomputable section
namespace GlobalTheory.PolarU.Conj
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
open scoped Kronecker

theorem conj_pow_of_mul_eq_one {n : Type} [Fintype n] [DecidableEq n] (A A' S : Matrix n n ℂ)
    (h : A * A' = 1) (m : ℕ) : (A * S * A') ^ m = A * S ^ m * A' := by
  have h' : A' * A = 1 := mul_eq_one_comm.mp h
  induction m with
  | zero => simp [h]
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    calc A * S ^ m * A' * (A * S * A') = A * S ^ m * (A' * A) * S * A' := by
          simp only [mul_assoc]
      _ = A * (S ^ m * S) * A' := by rw [h', mul_one]; simp only [mul_assoc]

theorem conj_tsum_of_mul_eq_one {n : Type} [Fintype n] [DecidableEq n] (A A' : Matrix n n ℂ)
    (h : A * A' = 1) (f : ℕ → Matrix n n ℂ) :
    A * (∑' m, f m) * A' = ∑' m, A * f m * A' := by
  have h' : A' * A = 1 := mul_eq_one_comm.mp h
  by_cases hf : Summable f
  · rw [← hf.tsum_mul_left A, ← (hf.mul_left A).tsum_mul_right A']
  · have hg : ¬ Summable (fun m => A * f m * A') := by
      intro hg
      apply hf
      have hs := (hg.mul_left A').mul_right A
      refine hs.congr (fun m => ?_)
      rw [show A' * (A * f m * A') * A = (A' * A) * f m * (A' * A) by simp only [mul_assoc],
        h', one_mul, mul_one]
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hg]
    simp

theorem submatrix_mul_of_left {n : Type} [Fintype n] (P : n → Prop) [DecidablePred P]
    (A S : Matrix n n ℂ) (hA : ∀ i j, P i → ¬ P j → A i j = 0) :
    (A * S).submatrix (Subtype.val : {i // P i} → n) (Subtype.val : {i // P i} → n) =
      A.submatrix Subtype.val (Subtype.val : {i // P i} → n) *
        S.submatrix Subtype.val Subtype.val := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have key : ∀ k ∈ (Finset.univ : Finset n), A (i : n) k * S k (j : n) ≠ 0 → P k := by
    intro k _ hk
    by_contra hPk
    exact hk (by rw [hA _ _ i.2 hPk, zero_mul])
  rw [← Finset.sum_filter_of_ne key]
  exact Finset.sum_subtype _ (by simp) (fun k => A (i : n) k * S k (j : n))

theorem submatrix_mul_of_right {n : Type} [Fintype n] (P : n → Prop) [DecidablePred P]
    (S A : Matrix n n ℂ) (hA : ∀ i j, ¬ P i → P j → A i j = 0) :
    (S * A).submatrix (Subtype.val : {i // P i} → n) (Subtype.val : {i // P i} → n) =
      S.submatrix Subtype.val (Subtype.val : {i // P i} → n) *
        A.submatrix Subtype.val Subtype.val := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have key : ∀ k ∈ (Finset.univ : Finset n), S (i : n) k * A k (j : n) ≠ 0 → P k := by
    intro k _ hk
    by_contra hPk
    exact hk (by rw [hA _ _ hPk j.2, mul_zero])
  rw [← Finset.sum_filter_of_ne key]
  exact Finset.sum_subtype _ (by simp) (fun k => S (i : n) k * A k (j : n))

variable {p q : ℕ}

theorem kron_noMix {k l : Mat p q} (hk : IsKC k) (hl : IsKC l) (i j : Ix p q × Ix p q)
    (h : ¬ (sameBlock i.1 i.2 ↔ sameBlock j.1 j.2)) : (k ⊗ₖ lᵀ) i j = 0 := by
  simp only [Matrix.kroneckerMap_apply, Matrix.transpose_apply]
  by_cases h1 : sameBlock i.1 j.1
  · have h2 : ¬ sameBlock j.2 i.2 := by
      intro h2
      apply h
      rcases i with ⟨a | a, b | b⟩ <;> rcases j with ⟨c | c, d | d⟩ <;> simp_all [sameBlock]
    rw [hl _ _ h2, mul_zero]
  · rw [hk _ _ h1, zero_mul]

theorem kron_mul_eq_one {k k' : Mat p q} (h : k * k' = 1) :
    (k ⊗ₖ k'ᵀ) * (k' ⊗ₖ kᵀ) = 1 := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul, h, Matrix.transpose_one,
    Matrix.one_kronecker_one]

theorem adMat_conj {k k' : Mat p q} (h : k * k' = 1) (Y : Mat p q) :
    adMat (k * Y * k') = (k ⊗ₖ k'ᵀ) * adMat Y * (k' ⊗ₖ kᵀ) := by
  have h1 : k'ᵀ * kᵀ = 1 := by rw [← Matrix.transpose_mul, h, Matrix.transpose_one]
  unfold adMat
  rw [Matrix.mul_sub, Matrix.sub_mul]
  simp only [← Matrix.mul_kronecker_mul]
  simp [h, h1, Matrix.transpose_mul, mul_assoc]

theorem sinhcAd_conj {k k' : Mat p q} (h : k * k' = 1) (Y : Mat p q) :
    sinhcAd (k * Y * k') = (k ⊗ₖ k'ᵀ) * sinhcAd Y * (k' ⊗ₖ kᵀ) := by
  unfold sinhcAd
  rw [adMat_conj h, conj_tsum_of_mul_eq_one _ _ (kron_mul_eq_one h)]
  refine tsum_congr (fun j => ?_)
  rw [conj_pow_of_mul_eq_one _ _ _ (kron_mul_eq_one h), Matrix.mul_smul, Matrix.smul_mul]

theorem polJ_conj (p q : ℕ) (k k' Y : Mat p q) (h : k * k' = 1) (hk : IsKC k) (hk' : IsKC k') :
    polJ (k * Y * k') = polJ Y := by
  unfold polJ
  rw [sinhcAd_conj h]
  have hK : ∀ i j : Ix p q × Ix p q, ¬ sameBlock i.1 i.2 → ¬ ¬ sameBlock j.1 j.2 →
      (k ⊗ₖ k'ᵀ) i j = 0 := fun i j hi hj => kron_noMix hk hk' i j (by tauto)
  have hK' : ∀ i j : Ix p q × Ix p q, ¬ ¬ sameBlock i.1 i.2 → ¬ sameBlock j.1 j.2 →
      (k' ⊗ₖ kᵀ) i j = 0 := fun i j hi hj => kron_noMix hk' hk i j (by tauto)
  have e1 : ((k ⊗ₖ k'ᵀ) * sinhcAd Y * (k' ⊗ₖ kᵀ)).submatrix (Subtype.val : PIx p q → _)
      Subtype.val = ((k ⊗ₖ k'ᵀ) * sinhcAd Y).submatrix (Subtype.val : PIx p q → _) Subtype.val *
        (k' ⊗ₖ kᵀ).submatrix Subtype.val Subtype.val :=
    submatrix_mul_of_right (fun ab : Ix p q × Ix p q => ¬ sameBlock ab.1 ab.2) _ _ hK'
  have e2 : ((k ⊗ₖ k'ᵀ) * sinhcAd Y).submatrix (Subtype.val : PIx p q → _) Subtype.val =
      (k ⊗ₖ k'ᵀ).submatrix (Subtype.val : PIx p q → _) Subtype.val *
        (sinhcAd Y).submatrix Subtype.val Subtype.val :=
    submatrix_mul_of_left (fun ab : Ix p q × Ix p q => ¬ sameBlock ab.1 ab.2) _ _ hK
  have e3 : ((k ⊗ₖ k'ᵀ) * (k' ⊗ₖ kᵀ)).submatrix (Subtype.val : PIx p q → _) Subtype.val =
      (k ⊗ₖ k'ᵀ).submatrix (Subtype.val : PIx p q → _) Subtype.val *
        (k' ⊗ₖ kᵀ).submatrix Subtype.val Subtype.val :=
    submatrix_mul_of_left (fun ab : Ix p q × Ix p q => ¬ sameBlock ab.1 ab.2) _ _ hK
  rw [kron_mul_eq_one h, Matrix.submatrix_one _ Subtype.val_injective] at e3
  have e5 := congrArg Matrix.det e3
  rw [Matrix.det_one, Matrix.det_mul] at e5
  rw [e1, e2, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← e5, one_mul]

end GlobalTheory.PolarU.Conj
