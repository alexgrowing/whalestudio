import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFirstCoords
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import ReciprocityTheory.SemistableReduction.SJCoreA
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop

noncomputable section

namespace GlobalTheory.SphereMeanNull

theorem exists_blockSphere_eval_ne_zero {B n : ℕ} (hn : 0 < n) {a : Fin B → ℕ}
    {g : MvPolynomial (Fin B × Fin n) ℂ} (hg0 : g ≠ 0) (hg : IsMultiHomogeneous a g) :
    ∃ u : BlockSphere B n, eval (blockPoint u) g ≠ 0 := by
  obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.mp hg0
  obtain ⟨z, hz1, hz⟩ := exists_torus_coeff_le g s
  set r : ℝ := (Real.sqrt n)⁻¹ with hrdef
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < r := inv_pos.mpr (Real.sqrt_pos.mpr hnR)
  have hr2 : r ^ 2 * n = 1 := by
    rw [hrdef, inv_pow, Real.sq_sqrt hnR.le, inv_mul_cancel₀ hnR.ne']
  let u : BlockSphere B n := fun b => ⟨WithLp.toLp 2 (fun j => (r : ℂ) * z (b, j)), by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, hz1, mul_one]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm, hr2,
      Real.sqrt_one]⟩
  have hbp : blockPoint u = fun p => (r : ℂ) * z p := rfl
  have heval : eval (blockPoint u) g = (r : ℂ) ^ (∑ b, a b) * eval z g := by
    rw [hbp]; exact eval_mul_of_isMultiHomogeneous hg _ z
  have hne : eval z g ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (norm_pos_iff.mpr hs) hz)
  exact ⟨u, by rw [heval]; exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hr.ne')) hne⟩

theorem blockSphereProb_zeroSet_eq_zero : ∀ (B n : ℕ) (a : Fin B → ℕ)
    (g : MvPolynomial (Fin B × Fin n) ℂ), 0 < n → g ≠ 0 → IsMultiHomogeneous a g →
    blockSphereProb B n {z | eval (blockPoint z) g = 0} = 0 := by
  intro B n a g hn hg0 hg
  obtain ⟨u, hu⟩ := exists_blockSphere_eval_ne_zero hn hg0 hg
  exact null_of_logBound hn ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable
    (blockSphere_logMean_bound ReciprocityTheory.MultiplicativeHeights.Closed.sj ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable hn B)
    a g u hg hu

end GlobalTheory.SphereMeanNull
