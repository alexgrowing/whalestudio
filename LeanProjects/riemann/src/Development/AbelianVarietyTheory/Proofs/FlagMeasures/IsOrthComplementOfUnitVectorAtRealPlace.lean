import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.StabUnfold

theorem ofReal_qEps_eq {n : ℕ} (ε : Fin n → Bool) (y : Fin n → ℂ) :
    ((qEps ε y : ℝ) : ℂ) = star y ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  unfold qEps Formalism.REAL.Jm
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : star (y i) * y i = ((‖y i‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.star_def, Complex.conj_mul']
  split_ifs <;> simp [← h]

theorem frame_inv_form (I : AutInst) (v : InfinitePlace I.F) :
    ((I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (I.ε v) * (I.P v)⁻¹ = I.J.map (I.φ v) := by
  have hd : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have h1 : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  rw [← I.P_spec v]
  calc ((I.P v)⁻¹)ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v) * (I.P v)⁻¹
      = (I.P v * (I.P v)⁻¹)ᴴ * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1]; simp

theorem isPerp_at_place (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E)
    (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf) (h : IsPerp D s x A xf) (v : InfinitePlace I.F) :
    qEps (I.ε v) (infVec I v x) = sgn ℝ s ∧
      star (infVec I v x) ᵥ* (Formalism.REAL.Jm (I.ε v) * infMat D v A) = 0 ∧
      (infMat D v A)ᴴ * Formalism.REAL.Jm (I.ε v) * infMat D v A = Formalism.REAL.Jm (D.ε v) := by
  obtain ⟨-, h1, h2, h3, -⟩ := h
  have hφ : ∀ a : I.E, I.φ v (star a) = star (I.φ v a) := fun a => I.cm.cmUnram.2.1 _ a
  have hF := frame_inv_form I v
  have hs : star (fun i => I.φ v (x i)) = fun i => I.φ v (star x i) := by
    funext i; simp [hφ]
  refine ⟨?_, ?_, ?_⟩
  · apply Complex.ofReal_injective
    rw [ofReal_qEps_eq, infVec, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hF, hs]
    have := congrArg (I.φ v) h1
    have e : ((sgn ℝ s : ℝ) : ℂ) = I.φ v (sgn I.E s) := by
      unfold sgn; split_ifs <;> simp
    rw [e, ← this]
    simp [dotProduct, mulVec, map_sum]
  · rw [infVec, infMat, star_mulVec, vecMul_vecMul]
    have e : ((I.P v)⁻¹)ᴴ * (Formalism.REAL.Jm (I.ε v) * ((I.P v)⁻¹ * A.map (I.φ v) * D.P v))
        = (I.J * A).map (I.φ v) * D.P v := by
      rw [Matrix.map_mul, ← hF]; simp only [Matrix.mul_assoc]
    rw [e, ← vecMul_vecMul, hs]
    have e2 : (fun i => I.φ v (star x i)) ᵥ* (I.J * A).map (I.φ v) = 0 := by
      funext j
      have := congrArg (I.φ v) (congrFun h2 j)
      simpa [vecMul, dotProduct, map_sum] using this
    rw [e2, zero_vecMul]
  · rw [← D.P_spec v, ← h3, Matrix.map_mul, Matrix.map_mul, ← hF, infMat,
      Matrix.conjTranspose_map (I.φ v) hφ, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]

end GlobalTheory.StabUnfold
