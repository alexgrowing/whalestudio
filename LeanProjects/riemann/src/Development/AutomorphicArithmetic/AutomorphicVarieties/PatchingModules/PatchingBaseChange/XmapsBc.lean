import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilMod

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.xmaps_bc :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] (R P : Type) [CommRing R] [Algebra O R] [IsNoetherianRing R] [CommRing P] [Algebra O P] [IsNoetherianRing P] (θ : R →ₐ[O] P) (X X0 : Type) [AddCommGroup X] [Module R X] [AddCommGroup X0] [Module P X0] (f : R) (φ : X0 →+ X) (ψ : X →+ X0), (∃ s : Finset X0, ∀ z, ∃ c : X0 → R, z = ∑ g ∈ s, θ (c g) • g) → (∀ (t : R) z, φ (θ t • z) = t • φ z) → (∀ (t : R) z, ψ (t • z) = θ t • ψ z) → (∀ z, φ (ψ z) = f • z) → (∀ z, ψ (φ z) = θ f • z) → ∃ (φ' : Til O O' P ⊗[P] X0 →+ Til O O' R ⊗[R] X) (ψ' : Til O O' R ⊗[R] X →+ Til O O' P ⊗[P] X0), (∀ t z, φ' (Til.map O' θ t • z) = t • φ' z) ∧ (∀ t z, ψ' (t • z) = Til.map O' θ t • ψ' z) ∧ (∀ z, φ' (ψ' z) = Til.ι O O' R f • z) ∧ ∀ z, ψ' (φ' z) = Til.map O' θ (Til.ι O O' R f) • z := by
  intro O O' _ _ _ _ R P _ _ _ _ _ _ θ X X0 _ _ _ _ f φ ψ hgen hφ hψ hφψ hψφ
  letI : Module R X0 := Module.compHom X0 θ.toRingHom
  haveI : Module.Finite R X0 := by
    refine ⟨?_⟩
    obtain ⟨s, hs⟩ := hgen
    refine ⟨s, ?_⟩
    rw [eq_top_iff]
    intro z _
    obtain ⟨c, hc⟩ := hs z
    rw [hc]
    refine Submodule.sum_mem _ (fun g hg => ?_)
    exact Submodule.smul_mem _ (c g) (Submodule.subset_span hg)
  obtain ⟨e, he1, he2⟩ := BC.til_mod O O' R P θ X0 (fun a m => rfl)
  let φL : X0 →ₗ[R] X :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun t z => hφ t z }
  let ψL : X →ₗ[R] X0 :=
    { toFun := ψ
      map_add' := ψ.map_add
      map_smul' := fun t z => hψ t z }
  let A := Til O O' R
  let Φ := LinearMap.baseChange A φL
  let Ψ := LinearMap.baseChange A ψL
  have hsc : ∀ (M : Type) [AddCommGroup M] [Module R M] (g : M →ₗ[R] M) (r : R), (∀ m, g m = r • m) →
      ∀ w : A ⊗[R] M, LinearMap.baseChange A g w = Til.ι O O' R r • w := by
    intro M _ _ g r hg w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      rw [LinearMap.baseChange_tmul, hg, ← Til.algebraMap_eq, ← TensorProduct.smul_tmul,
        TensorProduct.smul_tmul', smul_eq_mul, Algebra.smul_def]
    | add x y hx hy => rw [map_add, hx, hy, smul_add]
  have heinv : ∀ (t : A) (z : Til O O' P ⊗[P] X0), e.symm (Til.map O' θ t • z) = t • e.symm z := by
    intro t z
    apply e.injective
    rw [he2, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  refine ⟨Φ.toAddMonoidHom.comp e.symm.toAddMonoidHom, e.toAddMonoidHom.comp Ψ.toAddMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro t z
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe]
    rw [heinv, LinearMap.map_smul]
  · intro t z
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe]
    rw [LinearMap.map_smul, he2]
  · intro z
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe, AddEquiv.symm_apply_apply]
    have := hsc X (φL ∘ₗ ψL) f (fun m => hφψ m) z
    rw [LinearMap.baseChange_comp] at this
    exact this
  · intro z
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe]
    have := hsc X0 (ψL ∘ₗ φL) f (fun m => hψφ m) (e.symm z)
    rw [LinearMap.baseChange_comp] at this
    change e (Ψ (Φ (e.symm z))) = _
    rw [show Ψ (Φ (e.symm z)) = Til.ι O O' R f • e.symm z from this, he2, AddEquiv.apply_symm_apply]
