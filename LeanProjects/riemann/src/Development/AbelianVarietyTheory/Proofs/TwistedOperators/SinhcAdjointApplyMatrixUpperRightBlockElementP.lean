import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY

noncomputable section
namespace GlobalTheory.PolarU.SinhcPres
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

variable {p q : ℕ}

theorem ad_sq_pY (B C : Fin p → Fin q → ℂ) : ∃ D,
    pY B * (pY B * pY C - pY C * pY B) - (pY B * pY C - pY C * pY B) * pY B = pY D := by
  refine ⟨fun i j => (pY B * (pY B * pY C - pY C * pY B) - (pY B * pY C - pY C * pY B) * pY B)
    (Sum.inl i) (Sum.inr j), ?_⟩
  have hh : (pY B * (pY B * pY C - pY C * pY B) - (pY B * pY C - pY C * pY B) * pY B)ᴴ =
      pY B * (pY B * pY C - pY C * pY B) - (pY B * pY C - pY C * pY B) * pY B := by
    simp only [conjTranspose_sub, conjTranspose_mul, pY_conjTranspose]
    noncomm_ring
  ext a b
  rcases a with i | i <;> rcases b with j | j
  · simp [pY, pOf, Matrix.mul_apply, Fintype.sum_sum_type]
  · simp only [pY, pOf, fromBlocks_apply₁₂, of_apply]
  · have := congrFun (congrFun hh (Sum.inr i)) (Sum.inl j)
    rw [← this]
    rfl
  · simp [pY, pOf, Matrix.mul_apply, Fintype.sum_sum_type]

theorem adMat_pow_pY (B C : Fin p → Fin q → ℂ) (k : ℕ) : ∃ D,
    adMat (pY B) ^ (2 * k) *ᵥ vecM (pY C) = vecM (pY D) := by
  induction k with
  | zero => exact ⟨C, by simp⟩
  | succ k ih =>
    obtain ⟨D, hD⟩ := ih
    obtain ⟨E, hE⟩ := ad_sq_pY B D
    refine ⟨E, ?_⟩
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ', pow_succ', ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hD, adMat_mulVec, adMat_mulVec, hE]

theorem summable_sinhc {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    Summable fun k : ℕ => (((2 * k + 1).factorial : ℂ)⁻¹) • A ^ (2 * k) := by
  open scoped Matrix.Norms.Operator in
  refine Summable.of_norm_bounded (g := fun k : ℕ => ‖((k.factorial : ℂ)⁻¹) • (A ^ 2) ^ k‖)
    (NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) (A ^ 2)) fun k => ?_
  rw [norm_smul, norm_smul, ← pow_mul, norm_inv, norm_inv, Complex.norm_natCast,
    Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine inv_anti₀ (by exact_mod_cast k.factorial_pos) ?_
  exact_mod_cast Nat.factorial_le (by omega)

theorem hasSum_sAd (Y V : Mat p q) (a b : Ix p q) :
    HasSum (fun k : ℕ => (((2 * k + 1).factorial : ℂ)⁻¹) * (adMat Y ^ (2 * k) *ᵥ vecM V) (a, b))
      (sAd Y V a b) := by
  have h := (summable_sinhc (adMat Y)).hasSum
  let f : Matrix (Ix p q × Ix p q) (Ix p q × Ix p q) ℂ →+ ℂ :=
    { toFun := fun M => (M *ᵥ vecM V) (a, b)
      map_zero' := by simp
      map_add' := fun M N => by simp [Matrix.add_mulVec] }
  have hf : Continuous f := by
    show Continuous fun M : Matrix (Ix p q × Ix p q) (Ix p q × Ix p q) ℂ => (M *ᵥ vecM V) (a, b)
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have h2 := h.map f hf
  convert h2 using 1
  · funext k
    simp [f, Matrix.smul_mulVec]
  · rfl

theorem sAd_pY : ∀ (p q : ℕ) (B C : Fin p → Fin q → ℂ),
    sAd (pY B) (pY C) = pY (sP (pY B) C) := by
  intro p q B C
  choose D hD using adMat_pow_pY B C
  have h := hasSum_sAd (pY B) (pY C)
  simp only [hD, vecM] at h
  ext a b
  rcases a with i | i <;> rcases b with j | j
  · have := h (Sum.inl i) (Sum.inl j)
    simp only [pY, pOf, fromBlocks_apply₁₁, Matrix.zero_apply, mul_zero] at this ⊢
    exact this.unique hasSum_zero
  · rfl
  · have h1 := h (Sum.inr i) (Sum.inl j)
    have h2 := (h (Sum.inl j) (Sum.inr i)).star
    show _ = star (sAd (pY B) (pY C) (Sum.inl j) (Sum.inr i))
    refine h1.unique ?_
    convert h2 using 2 with k
    simp [pY, pOf]
  · have := h (Sum.inr i) (Sum.inr j)
    simp only [pY, pOf, fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero] at this ⊢
    exact this.unique hasSum_zero

end GlobalTheory.PolarU.SinhcPres
