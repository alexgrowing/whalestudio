import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

namespace DualFRep

theorem gram_transpose (k r : ℕ) : (Formalism.QuantumDeterminants.Hpk k r)ᵀ = Formalism.QuantumDeterminants.Hpk k r := by
  have h := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).1
  ext i j
  have h1 := congrFun (congrFun h i) j
  rw [conjTranspose_apply] at h1
  rw [transpose_apply, ← h1]
  simp only [Formalism.QuantumDeterminants.Hpk]
  split_ifs <;> simp

variable {n : ℕ}

theorem left_inv {H g : Matrix (Fin n) (Fin n) ℂ} (h2 : H * H = 1) (hg : gᴴ * H * g = H) :
    H * gᴴ * H * g = 1 := by
  calc H * gᴴ * H * g = H * (gᴴ * H * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, h2]

theorem inv_eq {H g : Matrix (Fin n) (Fin n) ℂ} (h2 : H * H = 1) (hg : gᴴ * H * g = H) :
    g⁻¹ = H * gᴴ * H :=
  Matrix.inv_eq_left_inv (left_inv h2 hg)

theorem entry_le {k r : ℕ} (g : Mx k r) (a b : Fin (2 * r + k + 1)) : ‖g a b‖ ≤ B.gN g := by
  unfold B.gN
  apply Real.le_sqrt_of_sq_le
  rw [← Complex.normSq_eq_norm_sq]
  calc Complex.normSq (g a b) ≤ ∑ j, Complex.normSq (g a j) :=
        Finset.single_le_sum (f := fun j => Complex.normSq (g a j))
          (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ b)
    _ ≤ ∑ i, ∑ j, Complex.normSq (g i j) :=
        Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (g i j))
          (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ a)

end DualFRep

open DualFRep in

theorem isFRep_dualM (k r : ℕ) : IsFRep (k := k) (r := r) dualM (Formalism.QuantumDeterminants.Hpk k r) 1 := by
  have h1 := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).1
  have h2 := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).2.1
  have h3 := gram_transpose k r
  have hmem : ∀ g ∈ GG k r, gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := fun g hg => hg
  generalize Formalism.QuantumDeterminants.Hpk k r = H at h1 h2 h3 hmem ⊢
  refine ⟨h1, h2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [dualM]
  · intro g hg h hh
    simp only [dualM]
    rw [Matrix.mul_inv_rev, Matrix.transpose_mul]
  · intro g hg
    have key : g⁻¹ * H * (g⁻¹)ᴴ = H := by
      rw [inv_eq h2 (hmem g hg)]
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, h1]
      calc H * gᴴ * H * H * (H * (g * H)) = H * (gᴴ * (H * H) * H * g) * H := by
            simp only [Matrix.mul_assoc]
        _ = H := by rw [h2, Matrix.mul_one, hmem g hg, h2, Matrix.one_mul]
    have e : ((g⁻¹)ᵀ)ᴴ = ((g⁻¹)ᴴ)ᵀ := rfl
    have := congrArg Matrix.transpose key
    rw [transpose_mul, transpose_mul, h3] at this
    simp only [dualM]
    rw [e, Matrix.mul_assoc, this]
  · intro i j
    have hc : Continuous (fun g : Mx k r => (H * gᴴ * H) j i) := by
      have : Continuous (fun g : Mx k r => H * gᴴ * H) :=
        (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
      exact this.matrix_elem j i
    refine hc.continuousOn.congr ?_
    intro g hg
    simp only [dualM, transpose_apply]
    rw [inv_eq h2 (hmem g hg)]
  · refine ⟨∑ p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1), ∑ b, ∑ a, ‖H p.2 a‖ * ‖H b p.1‖, ?_⟩
    intro g hg i j
    simp only [dualM, transpose_apply, pow_one]
    rw [inv_eq h2 (hmem g hg)]
    have hN : 0 ≤ B.gN g := Real.sqrt_nonneg _
    calc ‖(H * gᴴ * H) j i‖ = ‖∑ b, ∑ a, H j a * star (g b a) * H b i‖ := by
          simp only [Matrix.mul_apply, conjTranspose_apply, Finset.sum_mul]
      _ ≤ ∑ b, ∑ a, ‖H j a * star (g b a) * H b i‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => norm_sum_le _ _)
      _ ≤ ∑ b, ∑ a, ‖H j a‖ * ‖H b i‖ * B.gN g := by
          refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun a _ => ?_
          rw [norm_mul, norm_mul, norm_star, mul_right_comm]
          exact mul_le_mul_of_nonneg_left (entry_le g b a) (by positivity)
      _ = (∑ b, ∑ a, ‖H j a‖ * ‖H b i‖) * B.gN g := by simp only [Finset.sum_mul]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ hN
          exact Finset.single_le_sum
            (f := fun p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1) => ∑ b, ∑ a, ‖H p.2 a‖ * ‖H b p.1‖)
            (fun p _ => by positivity) (Finset.mem_univ (i, j))
  · intro g hg hu
    have hl : star g * g = 1 := (Matrix.mem_unitaryGroup_iff').1 hu
    have hinv : g⁻¹ = star g := Matrix.inv_eq_left_inv hl
    rw [Matrix.mem_unitaryGroup_iff]
    simp only [dualM]
    rw [hinv]
    have e : star ((star g)ᵀ) = gᵀ := by
      ext a b
      simp [Matrix.star_apply]
    rw [e, ← transpose_mul, (Matrix.mem_unitaryGroup_iff).1 hu, transpose_one]

end GlobalTheory
