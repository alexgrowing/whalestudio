import Mathlib
import Formalism.FockGram.StatementLat

open Matrix LinearMap Module MeasureTheory

noncomputable section

namespace Formalism.E

theorem covolumeEqSqrtDetGram : CovolGram := by
  intro E ι _ _ _ _ _ _ _ b
  classical

  have hc : Fintype.card (Fin (Module.finrank ℝ E)) = Fintype.card ι := by
    rw [Fintype.card_fin, Module.finrank_eq_card_basis b]
  let o : OrthonormalBasis ι ℝ E := (stdOrthonormalBasis ℝ E).reindex (Fintype.equivOfCardEq hc)
  have hfd : volume (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume),
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.volume_parallelepiped]
  have hcov : ZLattice.covolume (Submodule.span ℤ (Set.range b)) = |o.toBasis.det b| := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume (ZSpan.isAddFundamentalDomain b volume),
      measureReal_def, ZSpan.measure_fundamentalDomain b volume o.toBasis, hfd, mul_one,
      ENNReal.toReal_ofReal (abs_nonneg _)]

  have hg : Matrix.gram ℝ b = (o.toBasis.toMatrix b)ᵀ * o.toBasis.toMatrix b := by
    ext i j
    simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, Basis.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
    rw [← o.sum_inner_mul_inner (b i) (b j)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_comm (o k) (b i)]
  rw [hcov, hg, Matrix.det_mul, Matrix.det_transpose, ← sq, Real.sqrt_sq_eq_abs, Basis.det_apply]

end Formalism.E
