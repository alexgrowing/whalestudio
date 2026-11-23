import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin
open scoped ContDiff

noncomputable section
namespace GlobalTheory.TorFin.NilAdj

theorem exists_smul_of_ker {n : ℕ} (ψ φ : Fin n → ℂ) (h : ∀ w, φ ⬝ᵥ w = 0 → ψ ⬝ᵥ w = 0) :
    ∃ b : ℂ, ψ = b • φ := by
  classical
  by_cases hφ : φ = 0
  · refine ⟨0, ?_⟩
    funext i
    have := h (Pi.single i 1) (by simp [hφ])
    simpa using this
  · obtain ⟨i, hi⟩ : ∃ i, φ i ≠ 0 := by
      by_contra hc; push_neg at hc; exact hφ (funext hc)
    refine ⟨ψ ⬝ᵥ Pi.single i (φ i)⁻¹, ?_⟩
    funext j
    have hw := h (Pi.single j 1 - φ j • Pi.single i (φ i)⁻¹) (by
      simp [dotProduct_sub, dotProduct_smul, hi])
    simp [dotProduct_sub, dotProduct_smul] at hw
    simp only [Pi.smul_apply, smul_eq_mul, dotProduct_single] at hw ⊢
    linear_combination hw

theorem cube_eq_zero {n : ℕ} {J Y : Matrix (Fin n) (Fin n) ℂ} {x : Fin n → ℂ} (hY : Y ∈ nilRad J x) :
    Y * Y * Y = 0 := by
  obtain ⟨h1, h2, h3⟩ := hY
  apply Matrix.mulVec_injective
  funext v
  have hv : (star x ᵥ* J) ⬝ᵥ (Y *ᵥ v) = 0 := by rw [dotProduct_mulVec, h2, zero_dotProduct]
  obtain ⟨a, ha⟩ := h3 _ hv
  rw [← mulVec_mulVec, ← mulVec_mulVec, ha, mulVec_smul, h1, smul_zero, zero_mulVec]

theorem sq_mem {n : ℕ} {J Y : Matrix (Fin n) (Fin n) ℂ} {x : Fin n → ℂ} (hY : Y ∈ nilRad J x) :
    Y * Y ∈ nilRad J x := by
  obtain ⟨h1, h2, h3⟩ := hY
  refine ⟨by rw [← mulVec_mulVec, h1, mulVec_zero], by rw [← vecMul_vecMul, h2, zero_vecMul], fun v hv => ?_⟩
  obtain ⟨a, ha⟩ := h3 v hv
  exact ⟨0, by rw [← mulVec_mulVec, ha, mulVec_smul, h1, smul_zero, zero_smul]⟩

theorem adj_mem {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Jᴴ = J) (hdet : IsUnit J.det) {x : Fin n → ℂ}
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ nilRad J x) : J⁻¹ * Yᴴ * J ∈ nilRad J x := by
  obtain ⟨h1, h2, h3⟩ := hY
  have hsφ : star (star x ᵥ* J) = J *ᵥ x := by rw [star_vecMul, star_star, hJ]
  refine ⟨?_, ?_, fun v hv => ?_⟩
  · rw [← mulVec_mulVec, ← mulVec_mulVec, ← hsφ, ← star_vecMul, h2, star_zero, mulVec_zero]
  · rw [← vecMul_vecMul, ← vecMul_vecMul, vecMul_vecMul (star x) J, mul_nonsing_inv J hdet, vecMul_one,
      ← star_mulVec, h1, star_zero, zero_vecMul]
  · have hker : ∀ w, (star x ᵥ* J) ⬝ᵥ w = 0 → (star (J *ᵥ v) ᵥ* Y) ⬝ᵥ w = 0 := by
      intro w hw
      obtain ⟨a, ha⟩ := h3 w hw
      rw [← dotProduct_mulVec, ha, dotProduct_smul]
      have : star (J *ᵥ v) ⬝ᵥ x = 0 := by
        have e := star_dotProduct_star (star x) (J *ᵥ v)
        rw [star_star] at e
        rw [dotProduct_comm, e, dotProduct_comm, dotProduct_mulVec, hv, star_zero]
      rw [this, smul_zero]
    obtain ⟨b, hb⟩ := exists_smul_of_ker _ _ hker
    refine ⟨star b, ?_⟩
    have e : Yᴴ *ᵥ (J *ᵥ v) = star b • (J *ᵥ x) := by
      have := congrArg star hb
      rw [star_vecMul, star_star, star_smul, hsφ] at this
      exact this
    rw [← mulVec_mulVec, ← mulVec_mulVec, e, mulVec_smul, mulVec_mulVec, nonsing_inv_mul J hdet, one_mulVec]

theorem exp_sub_one_eq {n : ℕ} {Y : Matrix (Fin n) (Fin n) ℂ} (h : Y * Y * Y = 0) :
    NormedSpace.exp Y - 1 = Y + (1 / 2 : ℂ) • (Y * Y) := by
  have h3 : ∀ k, 3 ≤ k → Y ^ k = 0 := by
    intro k hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [pow_add, pow_three, ← mul_assoc, h, zero_mul]
  rw [NormedSpace.exp_eq_tsum ℂ]
  beta_reduce
  rw [tsum_eq_sum (s := Finset.range 3)]
  · simp [Finset.sum_range_succ, pow_two]
    abel
  · intro k hk
    simp at hk
    rw [h3 k hk, smul_zero]

theorem nilRad_adj_exp : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), Jᴴ = J → IsUnit J.det → ∀ (x : Fin n → ℂ)
    (Y : Matrix (Fin n) (Fin n) ℂ), Y ∈ nilRad J x → J⁻¹ * Yᴴ * J ∈ nilRad J x ∧ NormedSpace.exp Y - 1 ∈ nilRad J x := by
  intro n J hJ hdet x Y hY
  refine ⟨adj_mem hJ hdet hY, ?_⟩
  rw [exp_sub_one_eq (cube_eq_zero hY)]
  exact (nilRad J x).add_mem hY ((nilRad J x).smul_mem _ (sq_mem hY))

end GlobalTheory.TorFin.NilAdj
