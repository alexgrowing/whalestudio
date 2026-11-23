import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SummableUnitBounds.SBoundOf

open GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LocalUnramified

theorem exists_unit_eq_uniformizer_zpow_ord_mul (F : Type) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (a : Fˣ) :
    ∃ u : 𝒪[F]ˣ, (a : F) = (GLnLocal.uniformizer F : F) ^ ord (a : F) * ((u : 𝒪[F]) : F) := by
  have hϖ := irreducible_uniformizer F
  refine ⟨(unitsEquivIntProd hϖ a).2, ?_⟩
  have hx : a = unitsOfIntProd hϖ (unitsEquivIntProd hϖ a) := by
    rw [← unitsEquivIntProd_symm_apply, MulEquiv.symm_apply_apply]
  have h := coe_unitsOfIntProd hϖ (unitsEquivIntProd hϖ a).1 (unitsEquivIntProd hϖ a).2
  rw [Prod.mk.eta, ← hx, unitsEquivIntProd_fst hϖ a, toAdd_ofAdd] at h
  exact h

theorem sDg : Ad3.LU.SDg := by
  intro F _ _ _ _ a b c
  obtain ⟨u, hu⟩ := exists_unit_eq_uniformizer_zpow_ord_mul F a
  obtain ⟨v, hv⟩ := exists_unit_eq_uniformizer_zpow_ord_mul F b
  obtain ⟨w, hw⟩ := exists_unit_eq_uniformizer_zpow_ord_mul F c
  refine ⟨integralGLHom F 3 (Ad3.dg u v w), ⟨_, rfl⟩, ?_⟩
  apply Units.ext
  ext i j
  rw [Units.val_mul, coe_torusPow]
  fin_cases i <;> fin_cases j <;>
    simp [Ad3.dg, integralGLHom, Matrix.diagonal_mul, ← hu, ← hv, ← hw]

end GlobalTheory.CompanionTheory.LocalUnramified
