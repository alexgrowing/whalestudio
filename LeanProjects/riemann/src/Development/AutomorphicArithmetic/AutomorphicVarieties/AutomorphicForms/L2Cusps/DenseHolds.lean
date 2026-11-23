import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
import GroundTheory.AutomorphicForms.L2LocalComponents

theorem UpperTheory.V.KernelIndexFullLattice.dense_holds :
    UpperTheory.V.KernelIndexFullLattice.Dense :=
  fun _ _ _ _ μ₁ _ => GroundTheory.Automorphic.CuspidalSpectrum.topologicalClosure_map_centralCuspForms μ₁
