import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.CountableRationalPointsDoubled
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE

noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace GlobalTheory.EisBL.DoubledParabolic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n}

theorem incM_mul_inv (b : GL (Fin n ⊕ Fin n) E) : incM F b.1 * incM F (b⁻¹).1 = 1 := by
  unfold incM
  rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

theorem incM_inv_mul (b : GL (Fin n ⊕ Fin n) E) : incM F (b⁻¹).1 * incM F b.1 = 1 := by
  unfold incM
  rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

theorem inFrame_mul (b : GL (Fin n ⊕ Fin n) E) (x y : G2 σ Y) : inFrame b (x * y) = inFrame b x * inFrame b y := by
  unfold inFrame
  show incM F (b⁻¹).1 * (mat2 x * mat2 y) * incM F b.1 =
    incM F (b⁻¹).1 * mat2 x * incM F b.1 * (incM F (b⁻¹).1 * mat2 y * incM F b.1)
  calc incM F (b⁻¹).1 * (mat2 x * mat2 y) * incM F b.1
      = incM F (b⁻¹).1 * mat2 x * (incM F b.1 * incM F (b⁻¹).1) * mat2 y * incM F b.1 := by
        rw [incM_mul_inv, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem inFrame_one (b : GL (Fin n ⊕ Fin n) E) : inFrame b (1 : G2 σ Y) = 1 := by
  unfold inFrame
  show incM F (b⁻¹).1 * 1 * incM F b.1 = 1
  rw [Matrix.mul_one, incM_inv_mul]

theorem inFrame_inv_mul (b : GL (Fin n ⊕ Fin n) E) (x : G2 σ Y) : inFrame b x⁻¹ * inFrame b x = 1 := by
  rw [← inFrame_mul, inv_mul_cancel, inFrame_one]

theorem inFrame_inv (b : GL (Fin n ⊕ Fin n) E) (x : G2 σ Y) : inFrame b x⁻¹ = (inFrame b x)⁻¹ :=
  (Matrix.inv_eq_left_inv (inFrame_inv_mul b x)).symm

theorem continuous_inFrame (b : GL (Fin n ⊕ Fin n) E) : Continuous (inFrame (σ := σ) (Y := Y) b) := by
  have hm : Continuous fun g : G2 σ Y => mat2 g := Units.continuous_val.comp continuous_subtype_val
  exact (continuous_const.matrix_mul hm).matrix_mul continuous_const

variable (σ Y) in

def parLev {α : Type} [LinearOrder α] (b : GL (Fin n ⊕ Fin n) E) (lev : Fin n ⊕ Fin n → α) : Subgroup (G2 σ Y) where
  carrier := {x | ∀ i j, lev j < lev i → inFrame b x i j = 0}
  mul_mem' := by
    intro x y hx hy
    show Matrix.BlockTriangular (inFrame b (x * y)) lev
    rw [inFrame_mul]
    exact Matrix.BlockTriangular.mul hx hy
  one_mem' := by
    show Matrix.BlockTriangular (inFrame b (1 : G2 σ Y)) lev
    rw [inFrame_one]
    exact Matrix.blockTriangular_one
  inv_mem' := by
    intro x hx
    show Matrix.BlockTriangular (inFrame b x⁻¹) lev
    rw [inFrame_inv]
    have : Invertible (inFrame b x) := ⟨inFrame b x⁻¹, inFrame_inv_mul b x, by
      rw [← inFrame_mul, mul_inv_cancel, inFrame_one]⟩
    exact Matrix.blockTriangular_inv_of_blockTriangular hx

end GlobalTheory.EisBL.DoubledParabolic
