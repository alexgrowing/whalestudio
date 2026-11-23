import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ToMKMulInv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExistsMu

noncomputable section

open Finset MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}

lemma inv_conj_exp (k : KG ε) (X : Matrix (Fin n) (Fin n) ℂ) :
    (toMK k⁻¹ * NormedSpace.exp X * toMK k)⁻¹ = toMK k⁻¹ * NormedSpace.exp (-X) * toMK k := by
  apply Matrix.inv_eq_left_inv
  have hexp : NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl X)), neg_add_cancel,
      NormedSpace.exp_zero]
  calc toMK k⁻¹ * NormedSpace.exp (-X) * toMK k * (toMK k⁻¹ * NormedSpace.exp X * toMK k)
      = toMK k⁻¹ * NormedSpace.exp (-X) * (toMK k * toMK k⁻¹) * NormedSpace.exp X * toMK k := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [toMK_mul_inv', Matrix.mul_one, Matrix.mul_assoc (toMK k⁻¹), hexp, Matrix.mul_one,
          toMK_inv_mul']

lemma isMu_unique {lam : Fin n → ℝ} {μ μ' : Fin n → ℤ} (hμ : IsMu lam μ) (hμ' : IsMu lam μ') : μ' = μ :=
  funext fun a => by
    have h2 : ((μ' a : ℤ) : ℝ) = ((μ a : ℤ) : ℝ) := (hμ' a).trans (hμ a).symm
    exact_mod_cast h2

theorem psiM_exp_formula {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inP ε X) :
    PsiM T μ (NormedSpace.exp X) =
      ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
        ∫ k, PhiM μ (toMK k⁻¹ * NormedSpace.exp X * toMK k)⁻¹ • (T.op k * projW T * T.op k⁻¹) ∂(muK ε) := by
  have h1 := psiM_kexp T μ 1 hX
  rw [toMK_one', op_one', Matrix.one_mul, one_mul] at h1
  rw [h1, ← psM_exp_neg T μ hX]
  simp_rw [inv_conj_exp]
  rfl

end ReciprocityTheory.ChartRestriction.DS.S7
