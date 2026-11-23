import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom

theorem det_rowRep_eq_zpow : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (i j : ℕ) (c : Fin j → 𝓀[F]), GeneralLinearGroup.det (rowRep i j c) = uniformizerUnit F ^ ((i : ℤ) + j) := by
  intro F _ _ _ _ i j c
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_rowRep, Matrix.det_fin_two_of]
  have h : ((i : ℤ) + j) = ((i + j : ℕ) : ℤ) := by push_cast; rfl
  rw [h, zpow_natCast, Units.val_pow_eq_pow_val, coe_uniformizerUnit, pow_add]
  simp

end GlobalTheory.CompanionTheory.LFUDom
