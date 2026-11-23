import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV UpperTheory.Gal.Int.Geo TensorProduct

theorem UpperTheory.exists_basis_simultaneousEigenspace_of_equivariant_bijective :
    ∀ (l : ℕ) [Fact l.Prime] (V V' : Type 1) [AddCommGroup V] [Module ℚ_[l] V] [AddCommGroup V'] [Module ℚ_[l] V'] (Φ : V →ₗ[ℚ_[l]] V'), Function.Bijective Φ → ∀ (I : Type) (T : I → V →ₗ[ℚ_[l]] V) (T' : I → V' →ₗ[ℚ_[l]] V'), (∀ g, Φ ∘ₗ T g = T' g ∘ₗ Φ) → ∀ (L : Type) [Field L] [Algebra ℚ_[l] L] (θ : I → L) (d : ℕ) (b : Module.Basis (Fin d) L ↥(⨅ g, Module.End.eigenspace ((T g).baseChange L) (θ g))), ∃ b' : Module.Basis (Fin d) L ↥(⨅ g, Module.End.eigenspace ((T' g).baseChange L) (θ g)), ∀ i, (b' i).1 = Φ.baseChange L (b i).1 := by
  intro l _ V V' _ _ _ _ Φ hΦ I T T' hT L _ _ θ d b
  let e : V ≃ₗ[ℚ_[l]] V' := LinearEquiv.ofBijective Φ hΦ
  let eL : L ⊗[ℚ_[l]] V ≃ₗ[L] L ⊗[ℚ_[l]] V' := LinearEquiv.baseChange ℚ_[l] L V V' e
  have hcoe : ∀ x, eL x = Φ.baseChange L x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hcomm : ∀ g x, (T' g).baseChange L (Φ.baseChange L x) = Φ.baseChange L ((T g).baseChange L x) := by
    intro g x
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hT g]
  have hmap : (⨅ g, Module.End.eigenspace ((T g).baseChange L) (θ g)).map (eL : L ⊗[ℚ_[l]] V →ₗ[L] L ⊗[ℚ_[l]] V') = ⨅ g, Module.End.eigenspace ((T' g).baseChange L) (θ g) := by
    apply le_antisymm
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hz
      rw [Submodule.mem_iInf] at hx ⊢
      intro g
      have hxg := Module.End.mem_eigenspace_iff.1 (hx g)
      rw [Module.End.mem_eigenspace_iff, LinearEquiv.coe_coe, hcoe, hcomm, hxg, map_smul]
    · intro y hy
      refine Submodule.mem_map.2 ⟨eL.symm y, ?_, by simp⟩
      rw [Submodule.mem_iInf] at hy ⊢
      intro g
      have hyg := Module.End.mem_eigenspace_iff.1 (hy g)
      rw [Module.End.mem_eigenspace_iff]
      apply eL.injective
      have h1 := hcomm g (eL.symm y)
      rw [← hcoe, LinearEquiv.apply_symm_apply, hyg] at h1
      rw [map_smul, LinearEquiv.apply_symm_apply, hcoe, ← h1]
  refine ⟨b.map (eL.ofSubmodules _ _ hmap), fun i => ?_⟩
  rw [Module.Basis.map_apply, LinearEquiv.ofSubmodules_apply, hcoe]
