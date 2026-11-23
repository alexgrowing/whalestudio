import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexGrFreeFiniteAndExactAt

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

private theorem finite_of_exact_of_finite {R A B C : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : B →ₗ[R] C} (h : Function.Exact f g) (hA : Module.Finite R A)
    (hC : Module.Finite R C) : Module.Finite R B :=
  have := isNoetherian_of_range_eq_ker f g h.linearMap_ker_eq.symm
  inferInstance

theorem finite_cubeComplex_grCube_homology :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] [IsNoetherianRing R]
      (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
      [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
      [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M →
      ∀ n p, Module.Finite R ((cubeComplex (grCube ι ℳ n)).homology p) := by
  intro ι _ _ R _ _
  suffices key : ∀ (j p : ℕ), Fintype.card ι < p + j →
      ∀ (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
      [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
      [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M →
      ∀ n, Module.Finite R ((cubeComplex (grCube ι ℳ n)).homology p) by
    intro M _ _ _ _ ℳ _ _ hM n p
    exact key (Fintype.card ι + 1) p (by omega) M ℳ hM n
  intro j
  induction j with
  | zero =>
    intro p hp M _ _ _ _ ℳ _ _ _ n
    have := ModuleCat.subsingleton_of_isZero
      (isZero_cubeComplex_homology (grCube ι ℳ n) (p := p) hp)
    infer_instance
  | succ j ih =>
    intro p hp M _ _ _ _ ℳ _ _ hM n
    obtain ⟨r, d, g, hg, hs⟩ := exists_graded_surjection (ι := ι) ℳ
    let _ := grSubDecomposition (grFree ι R d) hg.isHomogeneous_ker
    have hK := ih (p + 1) (by omega) _ (grSub (grFree ι R d) (LinearMap.ker g)) inferInstance n
    have hF := (cubeComplex_grFree_finite_and_exactAt ι R r d).1 n p
    have hse := (hg.shortExact_ker hs).cubeComplex_shortExact n
    have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hse.homology_exact₃ p (p + 1) rfl)
    exact finite_of_exact_of_finite hex hF hK

end GlobalTheory
