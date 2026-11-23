import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexGrFreeFiniteAndExactAt

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem exactAt_quot_of_shortExact {R : Type} [CommRing R]
    {S : ShortComplex (CochainComplex (ModuleCat.{0} R) ℕ)} (hS : S.ShortExact) (p : ℕ)
    (h₂ : S.X₂.ExactAt p) (h₁ : S.X₁.ExactAt (p + 1)) : S.X₃.ExactAt p := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at h₁ h₂ ⊢
  exact (hS.homology_exact₃ p (p + 1) rfl).isZero_X₂ (h₂.eq_of_src _ _) (h₁.eq_of_tgt _ _)

theorem cubeComplex_grCube_exactAt_of_card_lt (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] [IsNoetherianRing R] (q : ℕ) :
    ∀ (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
      [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
      [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M →
      ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ p, Fintype.card ι < p + q →
        (cubeComplex (grCube ι ℳ n)).ExactAt p := by
  induction q with
  | zero =>
    intro M _ _ _ _ ℳ _ _ _
    exact ⟨0, fun n _ p hp => (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      (isZero_cubeComplex_homology _ hp)⟩
  | succ q ih =>
    intro M _ _ _ _ ℳ _ _ _
    obtain ⟨r, d, f, hf, hs⟩ := exists_graded_surjection (ι := ι) ℳ
    letI : Decomposition (grSub (grFree ι R d) (LinearMap.ker f)) :=
      grSubDecomposition _ hf.isHomogeneous_ker
    obtain ⟨a, ha⟩ := ih (LinearMap.ker f) (grSub (grFree ι R d) (LinearMap.ker f)) inferInstance
    obtain ⟨b, hb⟩ := (cubeComplex_grFree_finite_and_exactAt ι R r d).2
    refine ⟨max a b, fun n hn p hp => ?_⟩
    exact exactAt_quot_of_shortExact ((hf.shortExact_ker hs).cubeComplex_shortExact n) p
      (hb n (le_of_max_le_right hn) p) (ha n (le_of_max_le_left hn) (p + 1) (by omega))

theorem cubeComplex_grCube_exactAt_of_finite :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] [IsNoetherianRing R]
      (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
      [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
      [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M →
      ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ p, (cubeComplex (grCube ι ℳ n)).ExactAt p := by
  intro ι _ _ R _ _ M _ _ _ _ ℳ _ _ hM
  obtain ⟨n₀, h⟩ := cubeComplex_grCube_exactAt_of_card_lt ι R (Fintype.card ι + 1) M ℳ hM
  exact ⟨n₀, fun n hn p => h n hn p (by omega)⟩

end GlobalTheory
