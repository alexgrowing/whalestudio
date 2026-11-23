import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.LiftCmp

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

theorem UpperTheory.V.KernelIndexFullLattice.cmpForm_holds :
    UpperTheory.V.KernelIndexFullLattice.CmpForm := by
  intro E _ _ _ a μ _ μ₁ _ hp φ hφ
  have h := UpperTheory.V.KernelIndexFullLattice.liftCmp_holds E a μ μ₁ hp (cuspVecL μ₁ φ) (cuspQuot φ.2.1.isLeftInvariant)
    (by rw [toLp_cuspVecL]; exact coeFn_cuspToL2 μ₁ φ)
  refine h.trans (Filter.Eventually.of_forall fun g => ?_)
  show cuspQuot φ.2.1.isLeftInvariant (RightCosetSpace.mk _ (retractOne g)) = φ.1 g
  rw [cuspQuot_mk, coe_retractOne, ← map_inv]
  exact apply_mul_centralSection_of_mem hφ _ _
