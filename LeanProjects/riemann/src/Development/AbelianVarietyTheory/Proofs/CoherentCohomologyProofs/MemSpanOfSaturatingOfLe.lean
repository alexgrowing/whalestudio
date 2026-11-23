import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexGradedModuleExactAtOfLargeDegreeStatement

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem mem_span_of_saturating_of_le : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (r : ℕ) (d : Fin r → ℤ) (g : Fin r → M), (∀ l, g l ∈ ℳ (d l)) → (∀ (i : ι) (y : M), ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (Set.range g)) → (∀ y : M, (∀ i : ι, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y = 0) → y = 0) → ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ y ∈ ℳ n, y ∈ Submodule.span (MvPolynomial ι R) (Set.range g) := by
  intro ι _ _ R _ _ M _ _ _ _ ℳ _ _ r d g hg hsat hinj
  set K := Submodule.span (MvPolynomial ι R) (Set.range g) with hK
  have hhom : K.IsHomogeneous ℳ := isHomogeneous_span_gr ℳ (by
    rintro _ ⟨l, rfl⟩
    exact ⟨d l, hg l⟩)
  letI : Decomposition (grSub ℳ K) := grSubDecomposition ℳ hhom
  have hfin : Module.Finite (MvPolynomial ι R) K :=
    Module.Finite.span_of_finite _ (Set.finite_range g)
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.T.cubeComplex_gradedModule_exactAt_of_large_degree ι R K (grSub ℳ K) hfin
  refine ⟨n₀, fun n hn y hy => ?_⟩
  have hf := isGradedMap_subtype ℳ K
  have hb := (grAug_bijective_iff (ι := ι) (grSub ℳ K) n).2 ⟨hn₀ n hn 0, hn₀ n hn 1⟩
  haveI : IsIso (grCechMap hf n) := isIso_grCechMap hf
    (fun i m hm => ⟨0, by rw [(map_eq_zero_iff _ K.injective_subtype).1 hm, smul_zero]⟩)
    (fun i y => by simpa using hsat i y) n
  have hs : Function.Surjective (grHMap hf n 0).hom :=
    ((ConcreteCategory.isIso_iff_bijective (grHMap hf n 0)).1 inferInstance).2
  obtain ⟨z, hz⟩ := hs (grAug ι ℳ n ⟨y, hy⟩)
  obtain ⟨y₀, rfl⟩ := hb.2 z
  rw [grHMap_grAug] at hz
  have h0 : y - (y₀.1 : M) = 0 := hinj _ fun i => by
    have e : toHomLoc ℳ {i} n ⟨y, hy⟩ = toHomLoc ℳ {i} n (hf.piece n y₀) := by
      rw [← cechHomologyZeroIso_grAug ℳ n ⟨y, hy⟩ ⟨{i}, rfl⟩,
        ← cechHomologyZeroIso_grAug ℳ n (hf.piece n y₀) ⟨{i}, rfl⟩, hz]
    have e' : awayFrac M (xProd R {i}) 0 y = awayFrac M (xProd R {i}) 0 (y₀.1 : M) :=
      congrArg Subtype.val e
    rw [← sub_eq_zero, ← map_sub, awayFrac_eq_zero_iff] at e'
    simpa using e'
  rw [sub_eq_zero.1 h0]
  exact y₀.1.2

end GlobalTheory
