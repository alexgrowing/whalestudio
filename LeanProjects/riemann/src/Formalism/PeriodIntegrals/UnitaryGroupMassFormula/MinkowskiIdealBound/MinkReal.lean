import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiIdealBound.VecNormNonneg

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Module
open scoped Pointwise

noncomputable section

namespace PIW.MinkowskiIdealBound.MinkR

open scoped Classical

theorem algNorm_prod {A B : Type*} [CommRing A] [CommRing B] [Algebra ℝ A] [Algebra ℝ B]
    [Module.Free ℝ A] [Module.Finite ℝ A] [Module.Free ℝ B] [Module.Finite ℝ B] (x : A × B) :
    Algebra.norm ℝ x = Algebra.norm ℝ x.1 * Algebra.norm ℝ x.2 := by
  rw [Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_prodMap]
  congr 1

theorem algNorm_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Type*} [CommRing A] [Algebra ℝ A]
    [Module.Free ℝ A] [Module.Finite ℝ A] (x : ι → A) :
    Algebra.norm ℝ x = ∏ i, Algebra.norm ℝ (x i) := by
  simp_rw [Algebra.norm_apply]
  rw [← LinearMap.det_pi]
  congr 1

theorem algNorm_real (r : ℝ) : Algebra.norm ℝ r = r := by
  rw [Algebra.norm_self]
  rfl

variable {F : Type} [Field F] [NumberField F]

theorem abs_algNorm (x : mixedSpace F) : |Algebra.norm ℝ x| = mixedEmbedding.norm x := by
  rw [algNorm_prod, algNorm_pi, algNorm_pi, mixedEmbedding.norm_apply, prod_eq_prod_mul_prod]
  simp only [algNorm_real, Algebra.norm_complex_apply, abs_mul, Finset.abs_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [mult_isReal w, pow_one, normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [mult_isComplex w, normAtPlace_apply_of_isComplex w.2, Complex.sq_norm,
      abs_of_nonneg (Complex.normSq_nonneg _)]

theorem normAtPlace_ringEquiv (y : InfiniteAdeleRing F) (w : InfinitePlace F) :
    normAtPlace w (InfiniteAdeleRing.ringEquiv_mixedSpace F y) = ‖y w‖ := by
  by_cases hw : w.IsReal
  · rw [normAtPlace_apply_of_isReal hw, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _) _
  · have hc : w.IsComplex := not_isReal_iff_isComplex.mp hw
    rw [normAtPlace_apply_of_isComplex hc, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _) _

theorem norm_ringEquiv (y : InfiniteAdeleRing F) :
    mixedEmbedding.norm (InfiniteAdeleRing.ringEquiv_mixedSpace F y) = ‖y‖ := by
  rw [mixedEmbedding.norm_apply, InfiniteAdeleRing.norm_def]
  exact Finset.prod_congr rfl fun w _ => by rw [normAtPlace_ringEquiv]

def rmulL (M : Matrix (Fin 2) (Fin 2) (mixedSpace F)) :
    (Fin 2 → mixedSpace F) →ₗ[ℝ] (Fin 2 → mixedSpace F) :=
  (Matrix.toLin' M.transpose).restrictScalars ℝ

def bW : Basis (Σ _ : Fin 2, Free.ChooseBasisIndex ℤ (𝓞 F)) ℝ (Fin 2 → mixedSpace F) :=
  Pi.basis fun _ => latticeBasis F

instance bsW : BorelSpace (Fin 2 → mixedSpace F) := Pi.borelSpace

def B1 (F : Type) [Field F] [NumberField F] : Set (Fin 2 → mixedSpace F) :=
  Set.pi Set.univ fun _ : Fin 2 => convexBodyLT F (fun _ => 1)

end PIW.MinkowskiIdealBound.MinkR

end
