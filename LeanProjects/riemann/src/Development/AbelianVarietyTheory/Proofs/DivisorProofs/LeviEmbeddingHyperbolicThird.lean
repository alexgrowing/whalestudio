import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC

open Matrix

theorem blk_le_two (n₁ : ℕ) (i : Fin (1 + n₁ + 1)) : blk n₁ i ≤ 2 := by
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left a => simp [blk]
    | right k => simp [blk]
  | right a => simp [blk]

theorem blk_cases {n₁ : ℕ} (i : Fin (1 + n₁ + 1)) :
    (∃ a, i = Fin.castAdd 1 (Fin.castAdd n₁ a)) ∨ (∃ k, i = mid k) ∨ (∃ a, i = Fin.natAdd (1 + n₁) a) := by
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left a => exact Or.inl ⟨a, rfl⟩
    | right k => exact Or.inr (Or.inl ⟨k, rfl⟩)
  | right a => exact Or.inr (Or.inr ⟨a, rfl⟩)

theorem one_sub_four_mul_ne_zero {a b : ℕ} (ha : a ≤ 2) (hb : b ≤ 2) (hab : a + b ≠ 2) :
    (1 - 4 * (2⁻¹ : ℂ) ^ (a + b)) ≠ 0 := by
  interval_cases a <;> interval_cases b <;> first | exact absurd rfl hab | norm_num

theorem blk_support_of_mul_eq_one {n₁ : ℕ} {M N : Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) ℂ}
    (hM : ∀ i j, blk n₁ i + blk n₁ j ≠ 2 → M i j = 0) (hMN : M * N = 1) :
    ∀ i j, blk n₁ i + blk n₁ j ≠ 2 → N i j = 0 := by
  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) ℂ, D = diagonal fun i => (2 : ℂ) ^ blk n₁ i :=
    ⟨_, rfl⟩
  obtain ⟨Di, hDi⟩ : ∃ D : Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) ℂ, D = diagonal fun i => (2⁻¹ : ℂ) ^ blk n₁ i :=
    ⟨_, rfl⟩
  have hDDi : D * Di = 1 := by
    rw [hD, hDi, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; rw [← mul_pow]; norm_num
  have hMDi : M * Di = (4⁻¹ : ℂ) • (D * M) := by
    ext i j
    rw [hD, hDi, mul_diagonal, Matrix.smul_apply, diagonal_mul, smul_eq_mul]
    by_cases h : blk n₁ i + blk n₁ j = 2
    · have e : (2 : ℂ) ^ blk n₁ i = 4 * 2⁻¹ ^ blk n₁ j := by
        have : (2 : ℂ) ^ blk n₁ i * 2 ^ blk n₁ j = 4 := by rw [← pow_add, h]; norm_num
        rw [← this, mul_assoc, ← mul_pow]; norm_num
      rw [e]; ring
    · rw [hM i j h]; ring
  have hNM : N * M = 1 := mul_eq_one_comm.1 hMN
  have h1 : M * ((4 : ℂ) • (Di * N * Di)) = 1 := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hMDi, Matrix.smul_mul, Matrix.smul_mul, smul_smul,
      Matrix.mul_assoc D M N, hMN, Matrix.mul_one, hDDi]
    norm_num
  have key : N = (4 : ℂ) • (Di * N * Di) := by
    calc N = N * (M * ((4 : ℂ) • (Di * N * Di))) := by rw [h1, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hNM, Matrix.one_mul]
  intro i j hij
  have e := congrFun (congrFun key i) j
  rw [Matrix.smul_apply, hDi, mul_diagonal, diagonal_mul, smul_eq_mul] at e
  have h0 : (1 - 4 * (2⁻¹ : ℂ) ^ (blk n₁ i + blk n₁ j)) * N i j = 0 := by
    rw [pow_add]; linear_combination e
  exact (mul_eq_zero.1 h0).resolve_left (one_sub_four_mul_ne_zero (blk_le_two n₁ i) (blk_le_two n₁ j) hij)

theorem adj_frame_blockTri : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
    (∀ i j, σ (Y.J j i) = -Y.J i j) → n = n₁ + 2 → form σ Y.J H.x H.x = 0 → form σ Y.J H.y H.y = 0 → form σ Y.J H.x H.y = 1 →
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * Y.J * H.ι.map σ = Y₁.J → Y₁.J.det ≠ 0 →
    ∀ R : Matrix (Fin (1 + n₁ + 1)) (Fin n) E, frame H * R = 1 → R * frame H = 1 →
    ∀ c : E, c ≠ 0 → IsHermND σ (c • Y.J.map σ) → IsHermND σ (c • Y₁.J.map σ) →
    ∀ (τ : E →+* ℂ) (s : ℕ) (X : Matrix (Fin n) (Fin n) ℂ),
      (∀ i j, blk n₁ j < blk n₁ i + s → (R.map τ * X * (frame H).map τ) i j = 0) →
      ∀ i j, blk n₁ j < blk n₁ i + s → (R.map τ * adj ((c • Y.J.map σ).map τ) X * (frame H).map τ) i j = 0 := by
  intro F E _ _ _ _ _ σ h n n₁ Y Y₁ H hsk hn hxx hyy hxy horth hgram hdet1 R hQR hRQ c hc hA hA₁ τ s X hX i j hij
  have hσ : ∀ e, σ (σ e) = e := fun e => τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])
  have hQR' : (frame H).map τ * R.map τ = 1 := by
    rw [← Matrix.map_mul, hQR, Matrix.map_one _ τ.map_zero τ.map_one]
  have hRQ' : R.map τ * (frame H).map τ = 1 := by
    rw [← Matrix.map_mul, hRQ, Matrix.map_one _ τ.map_zero τ.map_one]
  have hAu : IsUnit ((c • Y.J.map σ).map τ).det := isUnit_det_map hA τ

  have hGf : ∀ a b, ((frame H)ᵀ * Y.J * (frame H).map σ) a b =
      form σ Y.J (fun r => frame H r a) (fun r => frame H r b) := by
    intro a b
    simp only [Matrix.mul_apply, form, dotProduct, mulVec, transpose_apply, map_apply, Finset.sum_mul, Finset.mul_sum,
      mul_assoc]
    exact Finset.sum_comm
  have hskew : ∀ u v : Fin n → E, form σ Y.J u v = -σ (form σ Y.J v u) := by
    intro u v
    simp only [form, dotProduct, mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hsk]; ring
  have hcol : ∀ k : Fin n₁, (fun r => H.ι r k) = H.ι *ᵥ Pi.single k 1 := by
    intro k; ext r; simp [mulVec, dotProduct, Pi.single_apply]
  have hGs : ∀ a b, blk n₁ a + blk n₁ b ≠ 2 → ((frame H)ᵀ * Y.J * (frame H).map σ) a b = 0 := by
    intro a b hab
    rw [hGf]
    rcases blk_cases a with ⟨a, rfl⟩ | ⟨k, rfl⟩ | ⟨a, rfl⟩ <;>
      rcases blk_cases b with ⟨b, rfl⟩ | ⟨l, rfl⟩ | ⟨b, rfl⟩ <;>
      simp only [block_matrix_mulVec_basis, blk_mid, blk_y, frame_alt, frame_mid, frame_y] at hab ⊢
    · exact hxx
    · rw [hcol, hskew, (horth _).1, map_zero, neg_zero]
    · exact absurd rfl hab
    · rw [hcol]; exact (horth _).1
    · exact absurd rfl hab
    · rw [hcol]; exact (horth _).2
    · exact absurd rfl hab
    · rw [hcol, hskew, (horth _).2, map_zero, neg_zero]
    · exact hyy

  have hA'e : ∀ a b, (((frame H).map τ)ᴴ * (c • Y.J.map σ).map τ * (frame H).map τ) a b =
      τ c * star (τ (((frame H)ᵀ * Y.J * (frame H).map σ) a b)) := by
    intro a b
    simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      transpose_apply, map_mul, map_sum, h.2.2.2, star_sum, star_mul', star_star, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  have hA's : ∀ a b, blk n₁ a + blk n₁ b ≠ 2 →
      (((frame H).map τ)ᴴ * (c • Y.J.map σ).map τ * (frame H).map τ) a b = 0 := by
    intro a b hab
    rw [hA'e, hGs a b hab, map_zero, star_zero, mul_zero]
  have hAB : (((frame H).map τ)ᴴ * (c • Y.J.map σ).map τ * (frame H).map τ) *
      (R.map τ * ((c • Y.J.map σ).map τ)⁻¹ * (R.map τ)ᴴ) = 1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((frame H).map τ) (R.map τ), hQR', Matrix.one_mul,
      ← Matrix.mul_assoc ((c • Y.J.map σ).map τ), Matrix.mul_nonsing_inv _ hAu, Matrix.one_mul, ← conjTranspose_mul,
      hRQ', conjTranspose_one]
  have hB's := blk_support_of_mul_eq_one hA's hAB
  have hcancel : ∀ {p : Type} (M : Matrix (Fin n) p ℂ), (R.map τ)ᴴ * (((frame H).map τ)ᴴ * M) = M := by
    intro p M
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, hQR', conjTranspose_one, Matrix.one_mul]
  have hid : R.map τ * adj ((c • Y.J.map σ).map τ) X * (frame H).map τ =
      (R.map τ * ((c • Y.J.map σ).map τ)⁻¹ * (R.map τ)ᴴ) * (R.map τ * X * (frame H).map τ)ᴴ *
        (((frame H).map τ)ᴴ * (c • Y.J.map σ).map τ * (frame H).map τ) := by
    simp only [adj, conjTranspose_mul, Matrix.mul_assoc, hcancel]
  rw [hid, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h1 : blk n₁ i + blk n₁ k = 2
  · by_cases h2 : blk n₁ l + blk n₁ j = 2
    · rw [conjTranspose_apply, hX l k (by omega), star_zero, mul_zero, zero_mul]
    · rw [hA's l j h2, mul_zero]
  · rw [hB's i k h1, zero_mul, zero_mul]

end GlobalTheory.LeviHC
