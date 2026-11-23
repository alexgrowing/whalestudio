import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.IntegralModuleBases.IntegralModuleBasisStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.IntegralModuleBases.NormGsoSqLeTwoPowMulOfValEqAdd
import ReciprocityTheory.ReducedBases.ExistsRedOf
import ReciprocityTheory.ReducedBases.PrefixProdGeOne

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases

open Finset InnerProductSpace Matrix ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open scoped MatrixOrder ComplexOrder

variable {d : ℕ}

lemma norm_fB_sq (A B : Matrix (Fin d) (Fin d) ℝ) (hAB : A = Bᴴ * B) (x : Fin d → ℤ) :
    ‖fB B x‖ ^ 2 = (fun i => (x i : ℝ)) ⬝ᵥ (A *ᵥ fun i => (x i : ℝ)) := by
  have h := Q_eq A B hAB x
  simp only [Q, polar] at h
  have h2 : ‖fB B x‖ ^ 2 = toReal x ⬝ᵥ (A *ᵥ toReal x) := by linarith
  exact h2

lemma det_toMatrix_sq (e : Module.Basis (Fin d) ℤ (Fin d → ℤ)) :
    (((Pi.basisFun ℤ (Fin d)).toMatrix e).det : ℝ) ^ 2 = 1 := by
  have h := (Pi.basisFun ℤ (Fin d)).toMatrix_mul_toMatrix_flip e
  have hu : IsUnit ((Pi.basisFun ℤ (Fin d)).toMatrix e).det :=
    isUnit_iff_exists_inv.mpr ⟨(e.toMatrix (Pi.basisFun ℤ (Fin d))).det,
      by rw [← Matrix.det_mul, h, Matrix.det_one]⟩
  rcases Int.isUnit_iff.mp hu with h1 | h1 <;> rw [h1] <;> norm_num

lemma det_gram_fB (A B : Matrix (Fin d) (Fin d) ℝ) (hAB : A = Bᴴ * B)
    (e : Module.Basis (Fin d) ℤ (Fin d → ℤ)) :
    (Matrix.gram ℝ fun i => fB B (e i)).det = A.det := by
  have hG : Matrix.gram ℝ (fun i => fB B (e i)) =
      (Matrix.of fun k j => ((e j k : ℤ) : ℝ))ᵀ * A * (Matrix.of fun k j => ((e j k : ℤ) : ℝ)) := by
    ext i j
    rw [Matrix.gram_apply, ← polar_eq A B hAB]
    simp only [polar, toReal, dotProduct, mulVec, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  have hE : (Matrix.of fun k j => ((e j k : ℤ) : ℝ)) =
      ((Pi.basisFun ℤ (Fin d)).toMatrix e).map (Int.cast : ℤ → ℝ) := by
    ext k j
    simp [Module.Basis.toMatrix_apply]
  have hsq := det_toMatrix_sq e
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hE, ← Int.cast_det]
  linear_combination A.det * hsq

theorem redGram_holds : RedGramStatement := by
  intro d A m D hA hm hmin hD
  obtain ⟨B, hAB⟩ : ∃ B : Matrix (Fin d) (Fin d) ℝ, A = Bᴴ * B := by
    refine ⟨CFC.sqrt A, ?_⟩
    have h0 : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef
    have hsa : IsSelfAdjoint (CFC.sqrt A) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)
    rw [← Matrix.star_eq_conjTranspose, hsa.star_eq, CFC.sqrt_mul_sqrt_self A h0]
  obtain ⟨e, hre⟩ := exists_red_of (fB B) (fun e => (li_basis A B hA hAB e).2) (hlow_of A B hA hAB)
  have hm' : ∀ i, m ≤ ‖fB B (e i)‖ ^ 2 := by
    intro i
    rw [norm_fB_sq A B hAB]
    exact hmin _ (e.ne_zero i)
  refine ⟨e, fun i => ?_, fun x i => ?_⟩
  · have h1 := red_norm_sq_le _ hre m D hm hm' (by rw [det_gram_fB A B hAB e]; exact hD) i
    rw [norm_fB_sq A B hAB] at h1
    exact h1
  · have h1 := red_coeff_sq_le _ hre m hm hm' (fun l => ((e.repr x l : ℤ) : ℝ)) i
    rw [← fB_expand B e x, norm_fB_sq A B hAB] at h1
    exact h1

end ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases

end
