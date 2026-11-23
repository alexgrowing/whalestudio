import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec

namespace GlobalTheory.UnipKill

open ReciprocityTheory.ChartRestriction.G.FD NumberField

theorem mul_rk1_self_of_scale {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    (G g : Matrix (Fin N) (Fin N) E) (ξ : Fin N → E) (ε : E) (hg : IsIsom G g)
    (hξ : g.mulVec ξ = ε • ξ) (hc : cc ε = ε) (h0 : ε ≠ 0) :
    g * rk1 G ξ ξ = ε ^ 2 • (rk1 G ξ ξ * g) := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  have h1 : g.mulVec (ε⁻¹ • ξ) = ξ := by
    rw [Matrix.mulVec_smul, hξ, smul_smul, inv_mul_cancel₀ h0, one_smul]
  have h2 : herm G (g.mulVec x) ξ = ε⁻¹ * herm G x ξ := by
    have h3 := hg x (ε⁻¹ • ξ)
    rw [h1, herm_smul_right, cc_inv, hc] at h3
    exact h3
  rw [← Matrix.mulVec_mulVec, one_add_smul_vecMulVec_mulVec, Matrix.mulVec_smul, hξ, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, one_add_smul_vecMulVec_mulVec, h2, smul_smul, smul_smul]
  congr 1
  field_simp

theorem mul_transvMat_of_scale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (G g : Matrix (Fin N) (Fin N) E) (ξ : Fin N → E) (ε : E), IsIsom G g → g.mulVec ξ = ε • ξ →
    cc ε = ε → ε ≠ 0 → ∀ α : E, g * transvMat G ξ α = transvMat G ξ (ε ^ 2 * α) * g := by
  intro E _ _ _ N G g ξ ε hg hξ hc h0 α
  rw [transvMat_eq, transvMat_eq, mul_add, add_mul, mul_one, one_mul, mul_smul_comm,
    smul_mul_assoc, mul_rk1_self_of_scale G g ξ ε hg hξ hc h0, smul_smul, mul_comm α]

end GlobalTheory.UnipKill
