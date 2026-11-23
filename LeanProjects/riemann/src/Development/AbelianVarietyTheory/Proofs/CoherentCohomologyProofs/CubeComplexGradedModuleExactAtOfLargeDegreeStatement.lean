import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexGradedModuleExactAtOfLargeDegree
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubeComplex_gradedModule_exactAt_of_large_degree : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M → ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ p, (cubeComplex (grCube ι ℳ n)).ExactAt p := by
  first | exact @GlobalTheory.cubeComplex_grCube_exactAt_of_finite | exact GlobalTheory.cubeComplex_grCube_exactAt_of_finite | (intros; apply GlobalTheory.cubeComplex_grCube_exactAt_of_finite <;> assumption)
