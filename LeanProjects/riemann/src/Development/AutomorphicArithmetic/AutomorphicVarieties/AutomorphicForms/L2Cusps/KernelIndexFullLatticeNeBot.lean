import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
import GroundTheory.AutomorphicForms.L2LocalComponents.NonEmpty

theorem UpperTheory.V.KernelIndexFullLattice.kernelIndexFullLattice_neBot :
    UpperTheory.V.KernelIndexFullLattice.NeBot := by
  intro K _ _ n μ₁ _ V _ hV hirr
  exact GroundTheory.Automorphic.CuspidalSpectrum.summandCuspForms_ne_bot μ₁ V hV hirr
