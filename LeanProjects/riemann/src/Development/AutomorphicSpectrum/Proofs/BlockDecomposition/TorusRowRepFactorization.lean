import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom

theorem torusPow_mul_rowRep_inv : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (a b : ℤ) (i j : ℕ) (c : Fin j → 𝓀[F]),
  torusPow F 2 ![a, b] * (rowRep i j c)⁻¹ =
    Ad3.uni2 (-(digitSum F j c) * (GLnLocal.uniformizer F : F) ^ (a - b - i)) * torusPow F 2 ![a - i, b - j] := by
  intro F _ _ _ _ a b i j c
  have h : (GLnLocal.uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  have e1 : (GLnLocal.uniformizer F : F) ^ (a - i) * (GLnLocal.uniformizer F : F) ^ i =
      (GLnLocal.uniformizer F : F) ^ a := by
    rw [← zpow_natCast, ← zpow_add₀ h, sub_add_cancel]
  have e2 : (GLnLocal.uniformizer F : F) ^ (b - j) * (GLnLocal.uniformizer F : F) ^ j =
      (GLnLocal.uniformizer F : F) ^ b := by
    rw [← zpow_natCast, ← zpow_add₀ h, sub_add_cancel]
  have e3 : (GLnLocal.uniformizer F : F) ^ (a - b - i) * (GLnLocal.uniformizer F : F) ^ b =
      (GLnLocal.uniformizer F : F) ^ (a - i) := by
    rw [← zpow_add₀ h]
    congr 1
    ring
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_rowRep, coe_torusPow, coe_torusPow]
  simp only [Ad3.uni2]
  have d : ∀ u v : ℤ, (diagonal fun k => (GLnLocal.uniformizer F : F) ^ (![u, v] k)) =
      !![(GLnLocal.uniformizer F : F) ^ u, 0; 0, (GLnLocal.uniformizer F : F) ^ v] := by
    intro u v
    ext r s
    fin_cases r <;> fin_cases s <;> simp
  rw [d, d]
  ext r s
  fin_cases r <;> fin_cases s <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination -e1
  · linear_combination (digitSum F j c * (GLnLocal.uniformizer F : F) ^ (a - b - i)) * e2 + digitSum F j c * e3
  · linear_combination -e2

end GlobalTheory.CompanionTheory.LFUDom
