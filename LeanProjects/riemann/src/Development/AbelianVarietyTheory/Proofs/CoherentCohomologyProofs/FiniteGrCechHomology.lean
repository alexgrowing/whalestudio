import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteCechHomologyOfFiniteCubeHomology
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FinitePieceOfPolyGradedSMul
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteHomologyCubeComplexGradedModuleStatement

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem finite_grCech_homology : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R]
    [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
    [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M →
      ∀ n p, Module.Finite R ((cechComplex (grCube ι ℳ n)).homology p) := by
  intro ι _ _ R _ _ M _ _ _ _ ℳ _ _ hM n p
  have h₀ : Module.Finite R (ℳ n) := finite_piece_of_polyGradedSMul ι R M ℳ hM n
  have h₁ : Module.Finite R ((grCube ι ℳ n).obj ∅) :=
    Module.Finite.equiv (homLocEmptyEquiv ι ℳ n)
  exact finite_cechHomology_of_finite_cubeHomology ι R (grCube ι ℳ n) h₁
    (GlobalTheory.T.finite_homology_cubeComplex_gradedModule ι R M ℳ hM n) p

end GlobalTheory
