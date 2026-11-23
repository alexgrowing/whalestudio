import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.LiftCmp

open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

theorem UpperTheory.V.KernelIndexFullLattice.cmpEquiv_holds :
    UpperTheory.V.KernelIndexFullLattice.CmpEquiv := by
  intro E _ _ _ a μ _ _ μ₁ _ hp g v
  rw [l2DiscreteQuotient_ext_iff_lift_ae_eq]
  have h1 := UpperTheory.V.KernelIndexFullLattice.liftCmp_holds E a μ μ₁ hp v _ (Filter.EventuallyEq.refl _ _)
  have h2 := (MeasureTheory.measurePreserving_mul_right μ g).quasiMeasurePreserving.ae h1
  have h3 : (toLp μ₁ (cuspRepT μ₁ (retractOne g) v) : RightCosetSpace (UpperTheory.V.KernelIndexFullLattice.Γ1 E a) → ℂ)
      =ᵐ[RightCosetSpace.quotientMeasure (UpperTheory.V.KernelIndexFullLattice.Γ1 E a) μ₁] fun x =>
        (toLp μ₁ v : RightCosetSpace (UpperTheory.V.KernelIndexFullLattice.Γ1 E a) → ℂ)
          (RightCosetSpace.rightMul (UpperTheory.V.KernelIndexFullLattice.Γ1 E a) (retractOne g) x) := by
    rw [toLp_cuspRepT]
    exact RightCosetSpace.coeFn_rightTranslate _ μ₁ (retractOne g) (toLp μ₁ v)
  have h4 := UpperTheory.V.KernelIndexFullLattice.liftCmp_holds E a μ μ₁ hp _ _ h3
  filter_upwards [lift_R g (UpperTheory.V.KernelIndexFullLattice.cmp hp v), h2, h4] with x hx1 hx2 hx4
  rw [hx1, hx4, hx2, RightCosetSpace.rightMul_mk, retractOne_mul]
