import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlanePairOfPair

open scoped Matrix
open Matrix

noncomputable section

namespace GlobalTheory.HyperbolicDecomp

open GlobalTheory.LeviTorusExists

section Gen

variable {R : Type} [CommRing R] {d : ℕ}

theorem gram_apply (c : R →+* R) (j : Matrix (Fin d) (Fin d) R) {m n : Type} [Fintype m] [Fintype n]
    (A : Matrix (Fin d) m R) (B : Matrix (Fin d) n R) (a : m) (b : n) :
    (Aᵀ * j * B.map c) a b = sesq c j (fun i => A i a) (fun i => B i b) := by
  simp only [sesq, Matrix.mul_apply, dotProduct, mulVec, transpose_apply, map_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end Gen

def colsMat {R : Type} {d d₁ : ℕ} (x y : Fin d → R) (ι : Matrix (Fin d) (Fin d₁) R) :
    Matrix (Fin d) (Fin d₁ ⊕ Fin 2) R :=
  Matrix.of fun i a => Sum.elim (fun k => ι i k) (fun l => ![x i, y i] l) a

theorem exists_coords {R : Type} [CommRing R] (c : R →+* R) (d₁ : ℕ)
    (j : Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) R) (j₁ : Matrix (Fin d₁) (Fin d₁) R) (x y : Fin (d₁ + 2) → R)
    (ι : Matrix (Fin (d₁ + 2)) (Fin d₁) R) (hcc : ∀ z, c (c z) = z) (hj : ∀ i k, c (j k i) = -j i k)
    (hxx : sesq c j x x = 0) (hyy : sesq c j y y = 0) (hxy : sesq c j x y = 1)
    (hι : ∀ z, sesq c j (ι *ᵥ z) x = 0 ∧ sesq c j (ι *ᵥ z) y = 0) (hj₁ : ιᵀ * j * ι.map c = j₁)
    (hdet : IsUnit j₁.det) (v : Fin (d₁ + 2) → R) : ∃ u, colsMat x y ι *ᵥ u = v := by
  classical
  set P := colsMat x y ι with hP
  have hyx : sesq c j y x = -1 := by rw [sesq_skew hcc hj, hxy, map_one]
  have hcol : ∀ k, (fun i => ι i k) = ι *ᵥ Pi.single k 1 := fun k => by
    rw [mulVec_single_one]; rfl
  have hιx : ∀ k, sesq c j (fun i => ι i k) x = 0 := fun k => by rw [hcol]; exact (hι _).1
  have hιy : ∀ k, sesq c j (fun i => ι i k) y = 0 := fun k => by rw [hcol]; exact (hι _).2
  have hxι : ∀ k, sesq c j x (fun i => ι i k) = 0 := fun k => by rw [sesq_skew hcc hj, hιx, map_zero, neg_zero]
  have hyι : ∀ k, sesq c j y (fun i => ι i k) = 0 := fun k => by rw [sesq_skew hcc hj, hιy, map_zero, neg_zero]
  have hG : Pᵀ * j * P.map c = fromBlocks j₁ 0 0 !![0, 1; -1, 0] := by
    ext a b
    rw [gram_apply]
    rcases a with k | l <;> rcases b with k' | l'
    · simp only [hP, colsMat, of_apply, Sum.elim_inl, fromBlocks_apply₁₁, ← hj₁, gram_apply]
    · simp only [fromBlocks_apply₁₂, Matrix.zero_apply]
      fin_cases l' <;> simp [hP, colsMat, hιx, hιy]
    · simp only [fromBlocks_apply₂₁, Matrix.zero_apply]
      fin_cases l <;> simp [hP, colsMat, hxι, hyι]
    · fin_cases l <;> fin_cases l' <;> simp [hP, colsMat, hxx, hyy, hxy, hyx]
  have hGdet : IsUnit (Pᵀ * j * P.map c).det := by
    rw [hG, det_fromBlocks_zero₂₁, det_fin_two_of]
    simpa using hdet
  let e : Fin d₁ ⊕ Fin 2 ≃ Fin (d₁ + 2) := finSumFinEquiv
  let Q : Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) R := P.submatrix id e.symm
  have hQ : Qᵀ * j * Q.map c = (Pᵀ * j * P.map c).submatrix e.symm e.symm := rfl
  have hQdet : IsUnit Q.det := by
    have h : IsUnit (Qᵀ * j * Q.map c).det := by rw [hQ, det_submatrix_equiv_self]; exact hGdet
    rw [det_mul, det_mul, det_transpose] at h
    exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h)
  refine ⟨fun a => (Q⁻¹ *ᵥ v) (e a), ?_⟩
  have hv : Q *ᵥ (Q⁻¹ *ᵥ v) = v := by rw [mulVec_mulVec, mul_nonsing_inv _ hQdet, one_mulVec]
  conv_rhs => rw [← hv]
  ext i
  simp only [mulVec, dotProduct, Q, submatrix_apply, id]
  exact (e.symm.sum_comp _).symm.trans (by simp)

theorem exists_decomp : ∀ (R : Type) [CommRing R] (c : R →+* R) (d d₁ : ℕ) (j : Matrix (Fin d) (Fin d) R) (j₁ : Matrix (Fin d₁) (Fin d₁) R) (x y : Fin d → R) (ι : Matrix (Fin d) (Fin d₁) R), (∀ z, c (c z) = z) → (∀ i k, c (j k i) = -j i k) → d = d₁ + 2 → GlobalTheory.LeviTorusExists.sesq c j x x = 0 → GlobalTheory.LeviTorusExists.sesq c j y y = 0 → GlobalTheory.LeviTorusExists.sesq c j x y = 1 → (∀ z, GlobalTheory.LeviTorusExists.sesq c j (ι *ᵥ z) x = 0 ∧ GlobalTheory.LeviTorusExists.sesq c j (ι *ᵥ z) y = 0) → ιᵀ * j * ι.map c = j₁ → IsUnit j₁.det → ∀ v : Fin d → R, ∃ z, v = GlobalTheory.LeviTorusExists.sesq c j v y • x - GlobalTheory.LeviTorusExists.sesq c j v x • y + ι *ᵥ z := by
  intro R _ c d d₁ j j₁ x y ι hcc hj hd hxx hyy hxy hι hj₁ hdet v
  subst hd
  classical
  obtain ⟨u, hu⟩ := exists_coords c d₁ j j₁ x y ι hcc hj hxx hyy hxy hι hj₁ hdet v
  have hyx : sesq c j y x = -1 := by rw [sesq_skew hcc hj, hxy, map_one]
  have hv : v = u (Sum.inr 0) • x + u (Sum.inr 1) • y + ι *ᵥ (fun k => u (Sum.inl k)) := by
    rw [← hu]
    ext i
    simp [colsMat, mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
    ring
  have h1 : sesq c j v y = u (Sum.inr 0) := by
    rw [hv]; simp [sesq_add_left, sesq_smul_left, hxy, hyy, (hι _).2]
  have h2 : sesq c j v x = -u (Sum.inr 1) := by
    rw [hv]; simp [sesq_add_left, sesq_smul_left, hxx, hyx, (hι _).1]
  refine ⟨fun k => u (Sum.inl k), ?_⟩
  rw [h1, h2, neg_smul, sub_neg_eq_add]
  exact hv

end GlobalTheory.HyperbolicDecomp
