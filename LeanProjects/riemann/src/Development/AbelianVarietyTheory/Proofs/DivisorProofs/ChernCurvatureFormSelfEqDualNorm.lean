import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

namespace GlobalTheory.CurvForm

theorem form_mulVec_left {g : ℕ} (K M : Matrix (Fin g) (Fin g) ℂ) (v w : Fin g → ℂ) :
    form K (M *ᵥ v) w = form (Mᵀ * K) v w := by
  simp only [form]
  rw [← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec]

theorem form_mulVec_right {g : ℕ} (K M : Matrix (Fin g) (Fin g) ℂ) (v w : Fin g → ℂ) :
    form K v (M *ᵥ w) = form (K * Mᴴᵀ) v w := by
  simp only [form]
  rw [star_mulVec, ← mulVec_transpose, mulVec_mulVec]

theorem form_curv_self_eq : ∀ (n g : ℕ) (H : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (z : Fin n → ℂ),
    MContDiffAt 2 H z → IsUnit (H z).det → (∀ᶠ x in 𝓝 z, (H x).IsSymm) →
    (∀ᶠ x in 𝓝 z, (H x).IsHermitian) → (∀ ξ η, mddbar H z ξ η = 0) →
    ∀ ξ v, form (H z) (curv H z ξ ξ *ᵥ v) v =
      form (H z)⁻¹ (mdel H z ξ *ᵥ v) (mdel H z ξ *ᵥ v) := by
  intro n g H z h2 hu hs hh hdd ξ v
  have hP : (mdel H z ξ)ᵀ = mdel H z ξ := by
    rw [← mdel_transpose, mdel_congr (hs.mono fun x hx => hx.eq)]
  have hQ : mdbar H z ξ = (mdel H z ξ)ᴴ := (conjTranspose_mdel hh ξ).symm
  have hHt : (H z)ᵀ = H z := hs.self_of_nhds.eq
  have hHi : (H z)⁻¹ᵀ = (H z)⁻¹ := by rw [transpose_nonsing_inv, hHt]
  rw [curv_eq h2 hu, hdd, transpose_zero, Matrix.mul_zero, sub_zero, hHt, hP, hQ]
  set P := mdel H z ξ with hPdef
  have hPc : Pᴴᵀ = Pᴴ := by
    ext i j
    have := congrFun (congrFun hP i) j
    simp only [transpose_apply, conjTranspose_apply] at this ⊢
    rw [this]
  simp only [form_mulVec_left, form_mulVec_right]
  congr 1
  rw [transpose_mul, transpose_mul, transpose_mul, hHi, hP, transpose_transpose, hPc,
    Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]

end GlobalTheory.CurvForm
