import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ContinuousConjProjection

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

lemma toMK_mul' (k k' : KG ε) : toMK (k * k') = toMK k * toMK k' := rfl

lemma toMK_one' : toMK (1 : KG ε) = 1 := rfl

lemma op_mul' (T : KType ε Λ) (k k' : KG ε) : T.op (k * k') = T.op k * T.op k' := by
  show ((T.τ (k * k') : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = _
  rw [map_mul]
  rfl

lemma op_one' (T : KType ε Λ) : T.op 1 = 1 := by
  show ((T.τ 1 : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = 1
  rw [map_one]
  rfl

lemma toMK_mul_inv' (k : KG ε) : toMK k * toMK k⁻¹ = 1 := by rw [← toMK_mul', mul_inv_cancel, toMK_one']

lemma toMK_inv_mul' (k : KG ε) : toMK k⁻¹ * toMK k = 1 := by rw [← toMK_mul', inv_mul_cancel, toMK_one']

theorem psiM_kexp (T : KType ε Λ) (μ : Fin n → ℤ) (k : KG ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) :
    PsiM T μ (toMK k * NormedSpace.exp X) = T.op k * psM T μ (NormedSpace.exp X) := by
  have h : ∃ (k' : KG ε) (X' : Matrix (Fin n) (Fin n) ℂ), inP ε X' ∧
      toMK k * NormedSpace.exp X = toMK k' * NormedSpace.exp X' := ⟨k, X, hX, rfl⟩
  obtain ⟨hk, hXX⟩ := polar_unique hX h.choose_spec.choose_spec.1 h.choose_spec.choose_spec.2
  rw [PsiM, dif_pos h, ← hXX, ← hk]

theorem psiM_equiv (T : KType ε Λ) (μ : Fin n → ℤ) (k₁ k₂ : KG ε) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    PsiM T μ (toMK k₁ * g * toMK k₂) = T.op k₁ * PsiM T μ g * T.op k₂ := by
  obtain ⟨k, X, hX, rfl⟩ := polar_exists hg
  obtain ⟨hX', hexp⟩ := inP_conj k₂⁻¹ hX
  rw [inv_inv] at hX' hexp
  have hc := psM_conj T μ k₂⁻¹ (NormedSpace.exp X)
  rw [inv_inv] at hc
  have hg' : toMK k₁ * (toMK k * NormedSpace.exp X) * toMK k₂ =
      toMK (k₁ * k * k₂) * NormedSpace.exp (toMK k₂⁻¹ * X * toMK k₂) := by
    rw [hexp, toMK_mul', toMK_mul']
    simp only [_root_.mul_assoc]
    rw [← _root_.mul_assoc (toMK k₂) (toMK k₂⁻¹), toMK_mul_inv', _root_.one_mul]
  rw [hg', psiM_kexp T μ _ hX', psiM_kexp T μ k hX, hexp, hc, op_mul', op_mul']
  simp only [_root_.mul_assoc]
  rw [← _root_.mul_assoc (T.op k₂) (T.op k₂⁻¹), ← op_mul', mul_inv_cancel, op_one', _root_.one_mul]

theorem psiM_one (T : KType ε Λ) (μ : Fin n → ℤ) : PsiM T μ 1 = 1 := by
  have h0 : inP ε (0 : Matrix (Fin n) (Fin n) ℂ) := by
    first | exact ⟨by simp [inG], by simp⟩ | exact ⟨by first | exact inG_zero ε | exact inG_zero, by simp⟩
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) = toMK (1 : KG ε) * NormedSpace.exp (0 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [toMK_one', NormedSpace.exp_zero, one_mul]
  rw [h1, psiM_kexp T μ 1 h0, op_one', one_mul, NormedSpace.exp_zero]
  first | exact psM_one T μ | exact psM_one | simp [psM_one]

end ReciprocityTheory.ChartRestriction.DS.S7
