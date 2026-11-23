import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.MulVecBvecApply
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomentParseval

lemma sum_norm_sq_eq {ι : Type} [Fintype ι] (v : ι → ℂ) :
    ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) = v ⬝ᵥ star v := by
  push_cast
  unfold dotProduct
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply, Complex.star_def, Complex.mul_conj']

lemma sum_vecMul {ι : Type} [Fintype ι] [DecidableEq ι] (V : Matrix ι ι ℂ) (hV : V * Vᴴ = 1) (y : ι → ℂ) :
    ∑ e, ‖(star y ᵥ* V) e‖ ^ 2 = ∑ i, ‖y i‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [sum_norm_sq_eq, sum_norm_sq_eq, Matrix.star_vecMul, star_star, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, hV, Matrix.one_mulVec, dotProduct_comm]

lemma inv_mem {k r : ℕ} {g : Mx k r} (hg : g ∈ GG k r) : g⁻¹ ∈ GG k r := by
  have e : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have h1 : g * g⁻¹ = 1 := PI.QuotSetU.UnitaryGroupMassFormula.SW.mul_inv_UH (k := k) (r := r) hg
  have h2 : (g⁻¹)ᴴ * gᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  show (g⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g⁻¹ = Formalism.QuantumDeterminants.Hpk k r
  calc (g⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * g⁻¹ := by rw [e]
    _ = ((g⁻¹)ᴴ * gᴴ) * Formalism.QuantumDeterminants.Hpk k r * (g * g⁻¹) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem sum_herm_sq : ∀ (k r : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : Mx k r → Matrix ι ι ℂ) (Γ U : Matrix ι ι ℂ) (d : ℕ) (om : ι → ℂ), IsFRep ρ Γ d → U ∈ Matrix.unitaryGroup ι ℂ → ∀ g ∈ GG k r, ∑ e, ‖Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ (fun c => U e c)) om‖ ^ 2 = ∑ i, ‖(ρ g⁻¹ *ᵥ om) i‖ ^ 2 := by
  intro k r ι _ _ ρ Γ U d om hρ hU g hg
  obtain ⟨hΓ, hΓ2, h1, hmul, hinv, -⟩ := hρ
  have hg' := inv_mem hg
  have hgg : g * g⁻¹ = 1 := PI.QuotSetU.UnitaryGroupMassFormula.SW.mul_inv_UH (k := k) (r := r) hg
  have hAB : ρ g * ρ g⁻¹ = 1 := by rw [← hmul g hg _ hg', hgg, h1]
  have hBA : (ρ g⁻¹)ᴴ * (ρ g)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hAB, Matrix.conjTranspose_one]
  have key : Γ * ρ g = (ρ g⁻¹)ᴴ * Γ := by
    calc Γ * ρ g = ((ρ g⁻¹)ᴴ * (ρ g)ᴴ) * Γ * ρ g := by rw [hBA, Matrix.one_mul]
      _ = (ρ g⁻¹)ᴴ * ((ρ g)ᴴ * Γ * ρ g) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hinv g hg]
  have hUU : Uᵀ * (Uᵀ)ᴴ = 1 := by
    have h0 : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff').1 hU
    have h3 := congrArg Matrix.transpose h0
    rw [Matrix.transpose_mul, Matrix.transpose_one] at h3
    exact h3
  have hV : (Γ * Uᵀ) * (Γ * Uᵀ)ᴴ = 1 := by
    rw [Matrix.conjTranspose_mul, hΓ, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hUU, Matrix.one_mul, hΓ2]
  rw [← sum_vecMul (Γ * Uᵀ) hV (ρ g⁻¹ *ᵥ om)]
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 2
  unfold Formalism.QuantumDeterminants.herm
  rw [Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul]
  rfl

end GlobalTheory.MomentParseval
