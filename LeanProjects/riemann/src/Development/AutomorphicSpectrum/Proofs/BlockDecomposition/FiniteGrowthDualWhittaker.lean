import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BndIUnits

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.GL2Factorization.DualGauge

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem tinv_mul (g h : GL (Fin 3) F) : GL2LocalData.tinv (g * h) = GL2LocalData.tinv g * GL2LocalData.tinv h := by
  apply Units.ext
  show ((g * h)⁻¹ : GL (Fin 3) F).valᵀ = (g⁻¹ : GL (Fin 3) F).valᵀ * (h⁻¹ : GL (Fin 3) F).valᵀ
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

def tinvHom : GL (Fin 3) F →* GL (Fin 3) F := MonoidHom.mk' GL2LocalData.tinv tinv_mul

theorem weyl_transposeInv_diag_GL3 (x y z : Fˣ) :
    (GL2LocalData.w3 : GL (Fin 3) F) * GL2LocalData.tinv (dg x y z) = dg z⁻¹ y⁻¹ x⁻¹ * GL2LocalData.w3 := by
  apply Units.ext
  have e : ((dg x y z : GL (Fin 3) F)⁻¹ : GL (Fin 3) F).val = (dg x y z : GL (Fin 3) F).inv := rfl
  show (GL2LocalData.w3 : GL (Fin 3) F).val * ((dg x y z : GL (Fin 3) F)⁻¹ : GL (Fin 3) F).valᵀ = _
  rw [e]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, GL2LocalData.w3, Matrix.mul_apply, Fin.sum_univ_three]

theorem weyl_GL3_mem_integralGL : (GL2LocalData.w3 : GL (Fin 3) F) ∈ integralGL F 3 := by
  refine (GLnLocal.mem_integralGL_iff F 3).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [GL2LocalData.w3, zero_mem, one_mem]
  · have e : ((GL2LocalData.w3 : GL (Fin 3) F)⁻¹ : GL (Fin 3) F).val = (GL2LocalData.w3 : GL (Fin 3) F).inv := rfl
    show ((GL2LocalData.w3 : GL (Fin 3) F)⁻¹ : GL (Fin 3) F).val i j ∈ _
    rw [e]
    fin_cases i <;> fin_cases j <;> simp [GL2LocalData.w3, zero_mem, one_mem]

end Local

end GlobalTheory.CompanionTheory.GL2Factorization.DualGauge
