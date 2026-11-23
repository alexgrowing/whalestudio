import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoreIsometryOfFixesIsotropicFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousCoreUnitaryGroupEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIsotropicUnipotentRadicalIffFrameStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem fixG_eq_unipRad_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ g ∈ fixG σ J C, ∃ u ∈ unipRad σ J C, ∃ x ∈ (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)), g = u * x ∧ (g ∈ ratPts σ J → x ∈ ratPts σ J) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF g hg
  obtain ⟨g₀, b, hgZ, -, -, hrat⟩ := GlobalTheory.T.exists_coreIsometry_of_fixes_isotropicFrame F E σ n J j m C D Z J₀ hF g hg
  obtain ⟨e, -, he, herat⟩ := GlobalTheory.T.exists_continuous_core_unitaryGroup_embedding F E σ n J j m C D Z J₀ hF
  obtain ⟨hxC, hxD, hxZ⟩ := he g₀
  set x := e g₀ with hx
  refine ⟨g * x⁻¹, ?_, x, ⟨hxC, hxD⟩, by group, fun h => herat g₀ (hrat h)⟩
  rw [GlobalTheory.T.mem_isotropicUnipotentRadical_iff_frame F E σ n J j m C D Z J₀ hF]
  have hxiC : x⁻¹ ∈ fixG σ J C := inv_mem hxC
  have hC' : (matHom _ σ J x⁻¹).1 * adMat F C = adMat F C := hxiC
  have hgC : (matHom _ σ J g).1 * adMat F C = adMat F C := hg

  have hxiZ : (matHom _ σ J x⁻¹).1 * adMat F Z = adMat F Z * (matHom _ σ J₀ g₀⁻¹).1 := by
    have h1 : (matHom _ σ J x⁻¹).1 * ((matHom _ σ J x).1 * adMat F Z) * (matHom _ σ J₀ g₀⁻¹).1
        = (matHom _ σ J x⁻¹).1 * (adMat F Z * (matHom _ σ J₀ g₀).1) * (matHom _ σ J₀ g₀⁻¹).1 := by rw [hxZ]
    rw [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.mul_one] at h1
    exact h1.symm
  refine ⟨?_, b * (matHom _ σ J₀ g₀⁻¹).1, ?_⟩
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, hC', hgC]
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, hxiZ, ← Matrix.mul_assoc, hgZ, Matrix.add_mul, Matrix.mul_assoc,
      ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.mul_one, Matrix.mul_assoc]

end GlobalTheory.SphEis
