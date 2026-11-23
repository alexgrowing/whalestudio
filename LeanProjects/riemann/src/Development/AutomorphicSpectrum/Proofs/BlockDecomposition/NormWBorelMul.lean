import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteAdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.GA
open scoped NumberField.AdeleRing Classical

namespace GlobalTheory.CompanionTheory.MajIwaK

variable {K : Type} [Field K] [NumberField K]

theorem eq_uni_mul_dg (β : Ad3.K.G3K K) (hβ : β ∈ (Reduction.adelicBorel : Subgroup (Ad3.K.G3K K)))
    (t1 t2 t3 : (𝔸[K])ˣ) (h1 : (β : Matrix (Fin 3) (Fin 3) 𝔸[K]) 0 0 = t1)
    (h2 : (β : Matrix (Fin 3) (Fin 3) 𝔸[K]) 1 1 = t2)
    (h3 : (β : Matrix (Fin 3) (Fin 3) 𝔸[K]) 2 2 = t3) :
    β = uni ((β : Matrix (Fin 3) (Fin 3) 𝔸[K]) 0 1 * ((t2⁻¹ : (𝔸[K])ˣ) : 𝔸[K]))
          ((β : Matrix (Fin 3) (Fin 3) 𝔸[K]) 0 2 * ((t3⁻¹ : (𝔸[K])ˣ) : 𝔸[K]))
          ((β : Matrix (Fin 3) (Fin 3) 𝔸[K]) 1 2 * ((t3⁻¹ : (𝔸[K])ˣ) : 𝔸[K])) * dg t1 t2 t3 := by
  have hb := Reduction.mem_adelicBorel.1 hβ
  have z10 : (β : Matrix (Fin 3) (Fin 3) 𝔸[K]) 1 0 = 0 := hb (by decide : (0 : Fin 3) < 1)
  have z20 : (β : Matrix (Fin 3) (Fin 3) 𝔸[K]) 2 0 = 0 := hb (by decide : (0 : Fin 3) < 2)
  have z21 : (β : Matrix (Fin 3) (Fin 3) 𝔸[K]) 2 1 = 0 := hb (by decide : (1 : Fin 3) < 2)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uni, dg, Matrix.mul_apply, Fin.sum_univ_three, h1, h2, h3, z10, z20, z21, mul_assoc]

theorem dg_eq_scalar_mul (t1 t2 t3 : (𝔸[K])ˣ) :
    (dg t1 t2 t3 : Ad3.K.G3K K) = dg t3 t3 t3 * dg (t1 * t2⁻¹ * (t2 * t3⁻¹)) (t2 * t3⁻¹) 1 := by
  apply Units.ext
  have e0 : t1 * t2⁻¹ * (t2 * t3⁻¹) = t1 * t3⁻¹ := by group
  have e1 : ((t3 : 𝔸[K])) * ((t1 * t3⁻¹ : (𝔸[K])ˣ) : 𝔸[K]) = t1 := by
    rw [← Units.val_mul, mul_comm t1, mul_inv_cancel_left]
  have e2 : ((t3 : 𝔸[K])) * ((t2 * t3⁻¹ : (𝔸[K])ˣ) : 𝔸[K]) = t2 := by
    rw [← Units.val_mul, mul_comm t2, mul_inv_cancel_left]
  rw [e0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dg, Matrix.mul_apply, Fin.sum_univ_three, -Units.val_mul, e1, e2]

theorem norm_W_borel_mul : ∀ (K : Type) [Field K] [NumberField K] (V : Submodule ℂ (Ad3.K.G3K K → ℂ)),
    Ad3.K.WhAK V → ∀ W ∈ V,
    ∀ β ∈ (Reduction.adelicBorel : Subgroup (Ad3.K.G3K K)), ∀ t1 t2 t3 : (𝔸[K])ˣ,
    (β : Matrix (Fin 3) (Fin 3) 𝔸[K]) 0 0 = t1 → (β : Matrix (Fin 3) (Fin 3) 𝔸[K]) 1 1 = t2 →
    (β : Matrix (Fin 3) (Fin 3) 𝔸[K]) 2 2 = t3 → ∀ k : Ad3.K.G3K K,
    ‖W (β * k)‖ = ‖W (Ad3.dg (t1 * t2⁻¹ * (t2 * t3⁻¹)) (t2 * t3⁻¹) 1 * k)‖ := by
  intro K _ _ V hV W hW β hβ t1 t2 t3 h1 h2 h3 k
  rw [eq_uni_mul_dg β hβ t1 t2 t3 h1 h2 h3, mul_assoc, hV.psi W hW, norm_mul, Circle.norm_coe,
    one_mul, dg_eq_scalar_mul t1 t2 t3, mul_assoc, hV.cen W hW]

end GlobalTheory.CompanionTheory.MajIwaK
