import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev

open scoped Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.PlaneRecon

theorem recon_of_pairings {E : Type} [Field E] {n n₁ : ℕ} (x y a b : Fin n → E) (ι C : Matrix (Fin n) (Fin n₁) E)
    (K : Matrix (Fin n₁) (Fin n₁) E) (hn : n = n₁ + 2) (hxa : x ⬝ᵥ a = 1) (hya : y ⬝ᵥ a = 0) (hxb : x ⬝ᵥ b = 0)
    (hyb : y ⬝ᵥ b = -1) (ha : a ᵥ* ι = 0) (hb : b ᵥ* ι = 0) (hx : Cᵀ *ᵥ x = 0) (hy : Cᵀ *ᵥ y = 0)
    (hK : K * (Cᵀ * ι) = 1) :
    Matrix.vecMulVec x a - Matrix.vecMulVec y b + ι * K * Cᵀ = 1 := by
  classical
  let P₀ : Matrix (Fin n) (Fin 2) E := Matrix.of fun i j => ![x i, y i] j
  let N₀ : Matrix (Fin 2) (Fin n) E := Matrix.of fun j i => ![a i, -b i] j
  have e : Fin 2 ⊕ Fin n₁ ≃ Fin n := Fintype.equivOfCardEq (by simp [hn, add_comm])
  have h11 : N₀ * P₀ = 1 := by
    rw [dotProduct_comm] at hxa hya hxb hyb
    simp only [dotProduct] at hxa hya hxb hyb
    ext i j
    fin_cases i <;> fin_cases j <;> simp [N₀, P₀, Matrix.mul_apply, hxa, hya, hxb, hyb]
  have h12 : N₀ * ι = 0 := by
    ext i j
    have h1 := congrFun ha j
    have h2 := congrFun hb j
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at h1 h2
    fin_cases i <;> simp [N₀, Matrix.mul_apply, h1, h2]
  have h21' : Cᵀ * P₀ = 0 := by
    ext i j
    have h1 := congrFun hx i
    have h2 := congrFun hy i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, Matrix.transpose_apply] at h1 h2
    fin_cases j <;> simp [P₀, Matrix.mul_apply, h1, h2]
  have h21 : K * Cᵀ * P₀ = 0 := by rw [Matrix.mul_assoc, h21', Matrix.mul_zero]
  have h22 : K * Cᵀ * ι = 1 := by rw [Matrix.mul_assoc, hK]
  have hNP : Matrix.fromRows N₀ (K * Cᵀ) * Matrix.fromCols P₀ ι = 1 := by
    rw [Matrix.fromRows_mul_fromCols, h11, h12, h21, h22, Matrix.fromBlocks_one]
  have hPN := (Matrix.mul_eq_one_comm_of_equiv e).1 hNP
  rw [Matrix.fromCols_mul_fromRows] at hPN
  rw [← hPN, Matrix.mul_assoc]
  congr 1
  ext i j
  simp [P₀, N₀, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMulVec_apply, sub_eq_add_neg]

theorem pair_swap {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = -J i j) (v w : Fin n → E) :
    (w ⬝ᵥ J *ᵥ fun i => σ (v i)) = -σ (v ⬝ᵥ J *ᵥ fun i => σ (w i)) := by
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  ring

theorem recon : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E), (∀ e, σ (σ e) = e) → ∀ (n n₁ : ℕ) (J : Matrix (Fin n) (Fin n) E) (J₁ : Matrix (Fin n₁) (Fin n₁) E) (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E), n = n₁ + 2 → (∀ i j, σ (J j i) = -J i j) → form σ J x x = 0 → form σ J y y = 0 → form σ J x y = 1 → (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) → ιᵀ * J * ι.map σ = J₁ → J₁.det ≠ 0 → Matrix.vecMulVec x (J *ᵥ fun i => σ (y i)) - Matrix.vecMulVec y (J *ᵥ fun i => σ (x i)) + ι * (J₁ᵀ)⁻¹ * (J * ι.map σ)ᵀ = 1 := by
  intro F E _ _ _ σ hσ n n₁ J J₁ x y ι hn hJ hxx hyy hxy hι hG hdet
  have hf : ∀ v w : Fin n → E, form σ J v w = v ⬝ᵥ J *ᵥ fun i => σ (w i) := fun _ _ => rfl
  simp only [hf] at hxx hyy hxy hι
  have hcol : ∀ k, ι *ᵥ Pi.single k 1 = fun i => ι i k := fun k => by
    ext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hrow : ∀ w : Fin n → E, (∀ u, ((ι *ᵥ u) ⬝ᵥ J *ᵥ fun i => σ (w i)) = 0) →
      (J *ᵥ fun i => σ (w i)) ᵥ* ι = 0 ∧ (J * ι.map σ)ᵀ *ᵥ w = 0 := by
    intro w hw
    constructor
    · ext k
      have h := hw (Pi.single k 1)
      rw [hcol, dotProduct_comm] at h
      exact h
    · ext k
      have h := pair_swap σ hσ J hJ (ι *ᵥ Pi.single k 1) w
      rw [hw, map_zero, neg_zero, hcol, dotProduct_comm] at h
      exact h
  obtain ⟨hx1, hx2⟩ := hrow x fun u => (hι u).1
  obtain ⟨hy1, hy2⟩ := hrow y fun u => (hι u).2
  refine recon_of_pairings x y _ _ ι _ _ hn hxy hyy hxx ?_ hy1 hx1 hx2 hy2 ?_
  · rw [pair_swap σ hσ J hJ x y, hxy, map_one]
  · have h : (J * ι.map σ)ᵀ * ι = J₁ᵀ := by
      rw [← hG, Matrix.mul_assoc, Matrix.transpose_mul ιᵀ, Matrix.transpose_transpose]
    rw [h]
    exact Matrix.nonsing_inv_mul _ (by rw [Matrix.det_transpose]; exact Ne.isUnit hdet)

end GlobalTheory.PlaneRecon
