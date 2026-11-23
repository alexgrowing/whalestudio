import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsBaseChangeAwayOfIntertwine
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsBaseChangeGradedPiece

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem map_xProd_pow_smul_of_X {ι R₀ R : Type} [CommRing R₀] [CommRing R] {N₀ N : Type}
    [AddCommGroup N₀] [Module (MvPolynomial ι R₀) N₀] [AddCommGroup N]
    [Module (MvPolynomial ι R) N] (ψ : N₀ → N)
    (hX : ∀ (i : ι) y, ψ ((X i : MvPolynomial ι R₀) • y) = (X i : MvPolynomial ι R) • ψ y)
    (s : Finset ι) (k : ℕ) (y : N₀) : ψ (xProd R₀ s ^ k • y) = xProd R s ^ k • ψ y := by
  classical
  have h1 : ∀ y, ψ (xProd R₀ s • y) = xProd R s • ψ y := by
    induction s using Finset.induction_on with
    | empty => intro y; simp
    | insert a s ha ih =>
      intro y
      rw [xProd, xProd, Finset.prod_insert ha, Finset.prod_insert ha, mul_smul, mul_smul, hX, ih]
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_succ', mul_smul, mul_smul, h1, ih]

theorem nonempty_baseChange_grCube_iso : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (N₀ : Type) [AddCommGroup N₀] [Module R₀ N₀] [Module (MvPolynomial ι R₀) N₀] [IsScalarTower R₀ (MvPolynomial ι R₀) N₀] (𝒩₀ : ℤ → Submodule R₀ N₀) [PolyGradedSMul ι 𝒩₀] [Decomposition 𝒩₀] (N : Type) [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N] [IsScalarTower R (MvPolynomial ι R) N] (𝒩 : ℤ → Submodule R N) [PolyGradedSMul ι 𝒩] [Decomposition 𝒩] [Module R₀ N] [IsScalarTower R₀ R N] [IsScalarTower R₀ (MvPolynomial ι R) N] (ψ : N₀ →ₗ[R₀] N) (n : ℤ), IsBaseChange R ψ → (∀ (i : ι) y, ψ ((X i : MvPolynomial ι R₀) • y) = (X i : MvPolynomial ι R) • ψ y) → (∀ j, ∀ y ∈ 𝒩₀ j, ψ y ∈ 𝒩 j) → Nonempty (Cube.baseChange R (grCube ι 𝒩₀ n) ≅ grCube ι 𝒩 n) := by
  intro ι _ _ R₀ R _ _ _ N₀ _ _ _ _ 𝒩₀ _ _ N _ _ _ _ 𝒩 _ _ _ _ _ ψ n hψ hX hgr
  choose θ hθ hθe using fun s : Finset ι => GlobalTheory.exists_isBaseChange_away_xProd ι R₀ R N₀ N ψ s hψ hX
  have hg : ∀ s j, ∀ y ∈ homLoc 𝒩₀ s j, θ s y ∈ homLoc 𝒩 s j := by
    rintro s j _ ⟨k, m, hm, rfl⟩
    rw [hθe]
    exact awayFrac_mem_homLoc (hgr _ _ hm) rfl
  let η : ∀ s, homLoc 𝒩₀ s n →ₗ[R₀] homLoc 𝒩 s n := fun s =>
    { toFun := fun y => ⟨θ s y, hg s n _ y.2⟩
      map_add' := fun a b => Subtype.ext (map_add (θ s) a.1 b.1)
      map_smul' := fun r a => Subtype.ext (map_smul (θ s) r a.1) }
  have hη : ∀ s, IsBaseChange R (η s) := fun s =>
    GlobalTheory.isBaseChange_gradedPiece R₀ R _ _ (homLoc 𝒩₀ s) (homLoc 𝒩 s) (θ s) n (η s) (hθ s) (hg s) fun _ => rfl
  have hres : ∀ {s t : Finset ι} (h : s ⊆ t) (z : homLoc 𝒩₀ s n),
      η t (homLocRes 𝒩₀ h n z) = homLocRes 𝒩 h n (η s z) := by
    rintro s t h ⟨_, k, m, hm, rfl⟩
    apply Subtype.ext
    change θ t (locRes X N₀ h (awayFrac N₀ _ k m)) = locRes X N h (θ s (awayFrac N₀ _ k m))
    rw [hθe, locRes_awayFrac X h (Finset.prod_sdiff h).symm,
      locRes_awayFrac X h (Finset.prod_sdiff h).symm, hθe]
    exact congrArg _ (map_xProd_pow_smul_of_X ψ hX (t \ s) k m)
  have key : ∀ {s t : Finset ι} (h : s ⊆ t) (x : R ⊗[R₀] homLoc 𝒩₀ s n),
      (hη t).equiv ((homLocRes 𝒩₀ h n).baseChange R x) = homLocRes 𝒩 h n ((hη s).equiv x) := by
    intro s t h x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul r z =>
      rw [LinearMap.baseChange_tmul, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul, map_smul,
        hres]
  exact ⟨Cube.isoMk (fun s => (hη s).equiv) fun h x => key h x⟩

end GlobalTheory
